# VBQueue Token Architecture

This document describes the token ownership structure, bridging patterns, and proof techniques
used in the Verus-verified VBQueue (SPSC lock-free ring buffer) implementation.

## 1. Token Architecture Overview

The verified VBQueue uses a 3-layer token architecture. Each layer exists because of
distinct ownership requirements imposed by Verus's `tokenized_state_machine!` and
`AtomicInvariant` mechanisms.

```
┌─────────────────────────────────────────────────────────────────────┐
│ Layer 1: Atomic Variable Tokens (inside AtomicInvariant, shared)   │
│                                                                     │
│   write, read, last, reserve, read_in_progress, write_in_progress  │
│   Each wrapped in GhostStuff<Perm, Tok> = { perm, token }         │
│   Accessed via fetch_add/store/load on PAtomicUsize/PAtomicBool    │
│   Tokens: VBQueue::write, VBQueue::read, etc.                     │
├─────────────────────────────────────────────────────────────────────┤
│ Layer 2: Local Tokens (exclusively owned by Producer/Consumer)      │
│                                                                     │
│   prod_token: VBQueue::producer  — owned by Producer struct        │
│   cons_token: VBQueue::consumer  — owned by Consumer struct        │
│   Carry local snapshots: write, reserve, last, read_obs, etc.     │
│   Persist across open_atomic_invariant! blocks                     │
│   Temporarily lent to GrantW/GrantR during active grants           │
├─────────────────────────────────────────────────────────────────────┤
│ Layer 3: Grant State Token (inside AtomicInvariant, with pool)     │
│                                                                     │
│   grant_state_token: VBQueue::grant_state                          │
│   Co-located with pool: PointsToRaw in GhostBufferPermission      │
│   Tracks prod_start/prod_end/cons_start/cons_end                   │
│   Invariant: pool.dom() == whole_set \ prod_set \ cons_set        │
└─────────────────────────────────────────────────────────────────────┘
```

### Key structs

- **`GhostStuff<Perm, Tok>`** (line 1077): Pairs an atomic permission with its state machine token.
  Used for each atomic variable's invariant.

- **`GhostBufferPermission`** (line 1108): Contains `pool: PointsToRaw` and `grant_state_token`.
  Its `wf` spec enforces the pool domain invariant:
  ```
  pool.dom() =~= Set::new(|i| whole_set.contains(i)
                              && !prod_set.contains(i)
                              && !cons_set.contains(i))
  ```

- **`VBBufferShared`** (line 1166): Holds references to all atomics plus `AtomicInvariant` wrappers
  for each layer's tokens. The `buf_perm_inv` invariant wraps `GhostBufferPermission`.

### Data flow during operations

```
Producer.grant_exact():
  prod_token (Layer 2) ──▶ open buf_perm_inv ──▶ mutate grant_state (Layer 3)
                                                  split pool ──▶ PointsToRaw to GrantW
  prod_token moves to GrantW

GrantW.commit():
  prod_token (from GrantW) ──▶ open buf_perm_inv ──▶ mutate grant_state (Layer 3)
                                                      join PointsToRaw back to pool
  prod_token returns to Producer

Consumer.read():
  cons_token (Layer 2) ──▶ open buf_perm_inv ──▶ mutate grant_state (Layer 3)
                                                  split pool ──▶ PointsToRaw to GrantR
  cons_token moves to GrantR

GrantR.release():
  cons_token (from GrantR) ──▶ open buf_perm_inv ──▶ mutate grant_state (Layer 3)
                                                      join PointsToRaw back to pool
  cons_token returns to Consumer
```

## 2. Why Duplication is Necessary

The token duplication across layers is a structural consequence of `tokenized_state_machine!`
and `AtomicInvariant` ownership rules.

### Constraint 1: `#[sharding(variable)]` generates independent ownership tokens

Each `#[sharding(variable)]` field in the state machine becomes an independently-owned token.
The state machine has 10 such fields:

```rust
#[sharding(variable)] pub write: nat,           // → VBQueue::write
#[sharding(variable)] pub read: nat,            // → VBQueue::read
#[sharding(variable)] pub last: nat,            // → VBQueue::last
#[sharding(variable)] pub reserve: nat,         // → VBQueue::reserve
#[sharding(variable)] pub read_in_progress: bool,
#[sharding(variable)] pub write_in_progress: bool,
#[sharding(variable)] pub already_split: bool,
#[sharding(variable)] pub producer: ProducerState,   // → VBQueue::producer
#[sharding(variable)] pub consumer: ConsumerState,   // → VBQueue::consumer
#[sharding(variable)] pub grant_state: GrantState,   // → VBQueue::grant_state
```

To call a state machine transition that `update`s a field, you must have `&mut` access to
that field's token. Different tokens can be in different ownership contexts.

### Constraint 2: Atomic variables need shared-access tokens

The `write`, `read`, `last`, `reserve`, `read_in_progress`, `write_in_progress` tokens must
live inside `AtomicInvariant`s because:
- Both producer and consumer access these atomics
- `AtomicInvariant` provides shared access via `open_atomic_invariant!`
- The token is paired with the atomic permission in `GhostStuff`

### Constraint 3: `producer`/`consumer` tokens need exclusive ownership

- `VBQueue::producer` must be exclusively owned by the `Producer` struct — only the producer
  thread calls transitions like `start_grant`, `do_reserve`, `store_write_at_commit`
- `VBQueue::consumer` must be exclusively owned by the `Consumer` struct — only the consumer
  thread calls `load_last_at_read`, `add_read_at_release`, `end_release`
- These cannot go into a shared `AtomicInvariant` because that would allow both threads to
  mutate them simultaneously

### Constraint 4: `grant_state` must be shared AND co-located with `PointsToRaw`

- `grant_state` tracks `prod_start/prod_end/cons_start/cons_end` — the byte ranges currently
  claimed by producer and consumer
- This must be co-located with `pool: PointsToRaw` because the pool invariant references
  `grant_state` values
- Both producer and consumer operations update `grant_state` (producer for prod_start/prod_end,
  consumer for cons_start/cons_end)
- Therefore `grant_state` must live inside a shared `AtomicInvariant` (the `buf_perm_inv`)

### Why `grant_state` can't merge with `producer`/`consumer`

Merging `grant_state` into `producer` would mean:
- Consumer operations (which update `cons_start`/`cons_end`) would need `&mut VBQueue::producer`
- But only the producer thread owns that token
- This breaks the SPSC ownership model

Similarly, splitting `grant_state` into two (one for prod, one for cons) won't work because:
- The pool invariant needs to reference both prod and cons ranges simultaneously
- `AtomicInvariant` can only protect a single value — splitting would require two invariants,
  but the pool must see both ranges atomically

### Conclusion

The 3-layer architecture is a necessary consequence of these constraints:
- Layer 1 tokens must be shared (both threads access atomics)
- Layer 2 tokens must be exclusive (SPSC ownership)
- Layer 3 must be shared AND co-located with pool (invariant coupling)

The "duplication" (e.g., `producer.write == write` and `grant_state.prod_start == producer.grant_start()`)
is maintained by state machine invariants and checked via readonly transitions.

## 3. Check Transitions (Readonly Bridging Transitions)

The state machine defines 14 `transition!` blocks with no `update` clauses — these are
readonly transitions that extract facts from the global invariants into local proof context.
They are critical for bridging information between the three token layers.

When you call e.g. `instance.check_grant_prod_eq(&prod_token, &grant_state_token)`, Verus
verifies the transition's `assert` clauses hold (they follow from the state machine invariants)
and makes them available as postconditions in the calling exec code.

### Category 1: Equality checks (Layer 1 ↔ Layer 2)

These extract that a local token's value matches the corresponding atomic variable:

| Transition | Asserts | Used by |
|-----------|---------|---------|
| `check_write_equality` | `producer.write == write`, `write <= length` | commit |
| `check_reserve_equality` | `producer.reserve == reserve`, `reserve <= length` | commit |
| `check_last_equality` | `producer.last == last`, `last <= length` | commit |
| `check_read_equality` | `consumer.read == read`, `read <= length` | read, release |
| `check_write_in_progress_equality` | `producer.write_in_progress == write_in_progress` | commit |
| `check_read_in_progress_equality` | `consumer.read_in_progress == read_in_progress` | (defined but unused) |

### Category 2: Bound/range checks (Layer 2 facts)

| Transition | Asserts | Used by |
|-----------|---------|---------|
| `check_read_is_le_last_in_inverted` | `read <= last_obs`, `read == pre.read` when inverted | read |
| `check_consumer_obs_in_range` | `write_obs <= length`, `last_obs <= length` | release |

### Category 3: Grant state checks (Layer 2 ↔ Layer 3) — **Most critical for pool proofs**

| Transition | Asserts | Used by |
|-----------|---------|---------|
| `check_grant_bounds_disjoint` | prod/cons ranges bounded and disjoint | grant, commit, read, release |
| `check_grant_prod_idle` | `write == reserve` → `prod_start == prod_end` | grant |
| `check_grant_cons_idle` | no write_obs/last_obs → `cons_start == cons_end` | (defined but unused) |
| `check_grant_cons_no_last` | no last_obs → `cons_start == cons_end` | read |
| **`check_grant_prod_eq`** | **`grant_state.prod_{start,end} == producer.grant_{start,end}()`** | **commit** |
| **`check_grant_cons_eq`** | **`grant_state.cons_{start,end} == consumer.grant_{start,end}()`** | **read, release** |

The last two (`check_grant_prod_eq` and `check_grant_cons_eq`) are the key enablers of the
Token Bridge Technique described in the next section.

## 4. Token Bridge Technique

This is the central proof pattern for pool management. It solves the problem of preserving
`PointsToRaw.dom()` knowledge across `open_atomic_invariant!` boundaries.

### The problem

When you open an `AtomicInvariant` and extract a `PointsToRaw`, you can establish its domain
from the invariant's `wf` spec. But after the invariant block closes, Z3 **forgets** all facts
about the `PointsToRaw.dom()` because the domain characterization was expressed in terms of
`grant_state_token.value()` — which was inside the invariant and is no longer in scope.

This matters when a function has **two successive** `open_atomic_invariant!` blocks (e.g.,
`commit` opens `buf_perm_inv` twice), and the second block needs to know the domain of a
`PointsToRaw` that was extracted or modified in the first block.

### The solution

Use `check_grant_prod_eq` or `check_grant_cons_eq` to re-express the `PointsToRaw.dom()` in
terms of the **local token** (`prod_token` or `cons_token`), which **persists outside** the
invariant block.

```rust
// Inside open_atomic_invariant! (first block):
proof {
    // Bridge: connect grant_state (Layer 3, inside invariant) to prod_token (Layer 2, outside)
    instance.check_grant_prod_eq(&prod_token, &grant_state_token);
    // Now Z3 knows: grant_state.prod_start == prod_token.value().grant_start()
    //               grant_state.prod_end   == prod_token.value().grant_end()

    // Express PointsToRaw.dom() in terms of prod_token (which persists after close)
    assert(extracted_ptr.dom() =~= set_int_range(
        base + prod_token.value().grant_start(),
        base + prod_token.value().grant_end()));
}
// After invariant closes:
// prod_token is still in scope, and Z3 remembers:
//   extracted_ptr.dom() =~= set_int_range(base + prod_token.value().grant_start(), ...)
// This fact carries into the second open_atomic_invariant! block.
```

### Why it works

1. `prod_token: VBQueue::producer` lives on the stack (Layer 2), not inside the invariant
2. `check_grant_prod_eq` establishes `grant_state.prod_start == prod_token.value().grant_start()`
3. The `assert(extracted_ptr.dom() =~= ...)` is expressed entirely in terms of `prod_token.value()`
4. After the invariant closes, Z3 retains the assertion because all its terms are still in scope
5. When the second invariant block opens, the assertion is available as a known fact

### When to apply

Apply the token bridge whenever:
- A `PointsToRaw` is extracted from or returned to the pool in one invariant block
- Its domain must be known in a subsequent invariant block
- The domain is characterized by `grant_state` values

## 5. Pool Domain Extensionality Pattern

After every state machine transition that modifies `grant_state`, the pool invariant must be
re-established: `pool.dom() =~= whole_set \ prod_set \ cons_set`. Z3 often cannot prove this
automatically, especially after `split`/`join` operations followed by token mutations.

### Standard pattern

```rust
// Step 1: Before the mutation, save the current pool domain characterization
// (Uses check_grant_bounds_disjoint to establish disjointness)
proof {
    instance.check_grant_bounds_disjoint(&grant_state_token);
    assert forall |i: int| current_pool.dom().contains(i) <==>
        (base <= i && i < base + len
         && !(base + old_ps <= i && i < base + old_pe)
         && !(base + old_cs <= i && i < base + old_ce)) by {};
}

// Step 2: Perform the mutation (e.g., store_write_at_commit)
// This changes grant_state values but not the PointsToRaw itself

// Step 3: After the mutation, prove the new characterization
// Requires bidirectional hints for Z3
assert forall |i: int| new_pool.dom().contains(i) <==>
    (whole_set.contains(i)
     && !new_prod_set.contains(i)
     && !new_cons_set.contains(i)) by {
    // → direction: if i is in pool, show it satisfies the formula
    if new_pool.dom().contains(i) {
        // Hint: i was in old pool or in returned PointsToRaw
        // Show it's in whole_set and not in new prod/cons sets
    }
    // ← direction: if i satisfies the formula, show it's in pool
    else {
        if (whole_set.contains(i) && !new_cons_set.contains(i)) {
            // Hint: if not in new prod set, derive from old pool characterization
        }
    }
};
```

### Why bidirectional hints are needed

Z3's quantifier instantiation works best when both directions of the `<==>` are hinted:
- **→ direction** (`pool.contains(i) ==> formula(i)`): Follows from how `split`/`join` compose domains
- **← direction** (`formula(i) ==> pool.contains(i)`): Often requires connecting old pool
  characterization to new one through the mutation

Without hints, Z3 may time out or fail to find the proof even though it's straightforward.

## 6. Pool Management Flow per Operation

Each VBQueue operation (grant, commit, read, release) involves one or more `open_atomic_invariant!`
blocks that interact with the pool via `PointsToRaw::split` and `PointsToRaw::join`.

| Operation | Invariant block | Pool action | PointsToRaw flow |
|-----------|----------------|-------------|-------------------|
| `grant_exact` | 1st `buf_perm_inv` | `split` prod region | pool → GrantW.points_to_raw_token |
| `commit` | 1st `buf_perm_inv` | `split` + `join` unused tail | GrantW partial → pool |
| `commit` | 2nd `buf_perm_inv` | `join` all remaining prod | GrantW rest → pool |
| `read` | 1st `buf_perm_inv` | `split` cons region | pool → local cons_points_to_raw |
| `read` | 2nd `buf_perm_inv` (wrap) | `join` old + `split` new | cons → pool → cons (wrapped) |
| `read` | (on failure) | `join` all cons | cons_points_to_raw → pool |
| `read` | (on success) | pass to GrantR | cons_points_to_raw → GrantR |
| `release` | 1st `buf_perm_inv` | `split` + `join` consumed | GrantR partial → pool |
| `release` | 2nd `buf_perm_inv` | `join` all remaining cons | GrantR rest → pool |

### `split` precondition pattern

Every `PointsToRaw::split(range)` requires `range.subset_of(self.dom())`. The standard proof:

```rust
assert(set_int_range(a, b).subset_of(pool.dom())) by {
    assert forall |i: int| set_int_range(a, b).contains(i)
        implies pool.dom().contains(i) by {
        // Z3 arithmetic: a <= i < b ==> i in pool.dom()
        // Uses disjointness (prod ∩ cons == ∅) and bounds
    };
};
```

### `join` postcondition

After `PointsToRaw::join(other)`, the result has `dom() == self.dom() + other.dom()`.
Both operands must have the same provenance. Disjointness is guaranteed by the pool invariant
(a region was split from pool and is now being returned).
