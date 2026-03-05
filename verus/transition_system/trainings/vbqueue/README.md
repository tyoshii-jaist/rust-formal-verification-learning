# VBQueue — Verus 形式検証付き SPSC ロックフリーリングバッファ

BBQueue (BipBuffer ベースの SPSC リングバッファ) を Verus の `tokenized_state_machine!` で形式検証した実装。

## ファイル構成

| ファイル | 内容 |
|---------|------|
| `vbqueue_inv.rs` | 状態機械定義 + exec コード + 証明 (メインファイル) |
| `ARCHITECTURE.md` | トークン構造・証明テクニックの詳細設計ドキュメント (英語) |

## トークン構造

`tokenized_state_machine!` の `#[sharding(variable)]` により、各フィールドが独立した所有権トークンになる。
これらは所有権の境界に応じて3層に分かれる。

```
Atomic変数 (各自のinvariant内)         ローカルトークン         共有トークン (buf_perm_inv内)
┌──────────────────────────┐      ┌──────────────┐      ┌──────────────────┐
│ write_token              │──────│              │      │                  │
│ reserve_token            │──────│ prod_token   │──────│ grant_state_token│
│ last_token               │──────│              │      │                  │
│ write_in_progress_token  │──────│              │      │   + pool         │
└──────────────────────────┘      └──────────────┘      │                  │
┌──────────────────────────┐      ┌──────────────┐      │                  │
│ read_token               │──────│ cons_token   │──────│                  │
│ read_in_progress_token   │──────│              │      │                  │
└──────────────────────────┘      └──────────────┘      └──────────────────┘
```

### 第1層: Atomic 変数トークン (共有、各 AtomicInvariant 内)

`write`, `read`, `last`, `reserve`, `read_in_progress`, `write_in_progress` の各 atomic 変数に対応。
`GhostStuff<Perm, Tok>` で atomic permission とトークンをペアにし、`AtomicInvariant` で包む。
Producer/Consumer 双方からアクセスされるため共有が必要。

### 第2層: ローカルトークン (Producer/Consumer が排他的に所有)

- `prod_token: VBQueue::producer` — Producer 構造体が所有
- `cons_token: VBQueue::consumer` — Consumer 構造体が所有

ローカルなスナップショット (`write`, `reserve`, `read_obs` 等) を保持する。
`open_atomic_invariant!` ブロックの外側で生存するため、Token Bridge の鍵となる。

### 第3層: Grant State トークン (buf_perm_inv 内、pool と同居)

`grant_state_token: VBQueue::grant_state` は `GhostBufferPermission` 内で `pool: PointsToRaw` と同居する。
`prod_start/prod_end/cons_start/cons_end` を追跡し、pool の不変条件を維持する:

```
pool.dom() == whole_set \ prod_set \ cons_set
```

### なぜ3層が必要か

- 第1層は共有が必要 (両スレッドが atomic にアクセス)
- 第2層は排他所有が必要 (SPSC の所有権モデル)
- 第3層は共有かつ pool と同居が必要 (不変条件の結合)

`grant_state` を `producer`/`consumer` に統合できない理由: Producer の操作が `cons_start/cons_end` を、Consumer の操作が `prod_start/prod_end` を参照する必要があるが、相手のトークンにはアクセスできない。

## Token Bridge テクニック

`open_atomic_invariant!` を閉じると、Z3 は invariant 内部のオブジェクトに関する事実を忘れる。
しかし次の invariant ブロックで `PointsToRaw.dom()` を知る必要がある。

解決策: invariant 内で `check_grant_prod_eq` / `check_grant_cons_eq` を呼び、`PointsToRaw.dom()` をローカルトークン (第2層) の値で表現する。ローカルトークンは invariant の外側で生存するため、Z3 はこの事実を保持できる。

## Pool 管理フロー

| 操作 | Pool への作用 | PointsToRaw の流れ |
|-----|-------------|-------------------|
| grant_exact | split | pool → GrantW |
| commit (sub_reserve) | split + join | GrantW 未使用分 → pool |
| commit (store_write) | join | GrantW 残り → pool |
| read (load_last) | split | pool → GrantR |
| read (wrap_read) | join + split | GrantR → pool → GrantR |
| read_fail | join | GrantR → pool |
| release (add_read) | split + join | GrantR 消費分 → pool |
| release (end_release) | join | GrantR 残り → pool |

## 詳細

トークン構造、check transition の一覧、証明パターンの詳細は [ARCHITECTURE.md](./ARCHITECTURE.md) を参照。
