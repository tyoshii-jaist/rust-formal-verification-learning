use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::raw_ptr::MemContents;
use vstd::assert_by_contradiction;

verus!{
struct Node<V> {
    next: Option<PPtr<Node<V>>>,
    payload: V,
}

// Singly-linked list
// Contains head pointer, tail pointer
// and in ghost code, tracks all the pointers and all the PointsTo permissions
// to access the nodes
pub struct SinglyLinkedList<V> {
    // physical data:
    head: Option<PPtr<Node<V>>>,

    // ghost and tracked data:
    ghost_state: Tracked<GhostState<V>>,
}

// tracked は ghost なのでコンパイルされない。ghost と tracked の違い: https://verus-lang.github.io/verus/guide/reference-var-modes.html
// tracked は proof に対応。ghost は spec に対応。
pub tracked struct GhostState<V> {
    ghost ptrs: Seq<PPtr<Node<V>>>, // Node へのポインタの配列
    // nat と PointsTo の Map。
    // PointsTo を理解しないと辛そう
    // PointsTo https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html
    // The PointsTo object represents both the ability to access (read or write) the data behind the pointer and the ability to free it (return it to the memory allocator).
    // The perm: PointsTo<V> object tracks two pieces of data:
    // perm.pptr() is the pointer that the permission is associated to.
    // perm.mem_contents() is the memory contents, which is one of either:
    // MemContents::Uninit if the memory pointed-to by by the pointer is uninitialized.
    // MemContents::Init(v) if the memory points-to the the value v.
    // Your access to the PointsTo object determines what operations you can safely perform with the pointer:

    // You can read from the pointer as long as you have read access to the PointsTo object, e.g., &PointsTo<V>.
    // You can write to the pointer as long as you have mutable access to the PointsTo object, e.g., &mut PointsTo<V>
    // You can call free to deallocate the memory as long as you have full onwership of the PointsTo object (i.e., the ability to move it).
    // For those familiar with separation logic, the PointsTo object plays a role similar to that of the “points-to” operator, ptr ↦ value.
    tracked points_to_map: Map<nat, PointsTo<Node<V>>>, 
}

impl<V> SinglyLinkedList<V> {
    pub fn new() -> (s: Self) {
        SinglyLinkedList {
            head: None,
            ghost_state: Tracked(GhostState {
                ptrs: Seq::empty(),
                points_to_map: Map::tracked_empty(),
            })
        }
    }

    pub fn push_front(&mut self, v: V) {
        // 新たに追加する v 用の PPtr と、Tracked を作る
        let (new_head_ptr, Tracked(new_head_pointsto)) = PPtr::<Node<V>>::new(
            Node::<V> {
                next: None,
                payload: v
            },
        );

        match self.head {
            None => {
                self.head = Some(new_head_ptr);
            },
            Some(old_head_ptr) => {
                self.head = Some(new_head_ptr);

                // ghost_stateのメンテ
                // たぶんここはひとつずらすということをやっていると思うが、もう少し読み込みが必要
                self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                    Map::<nat, nat>::new(
                        |j: nat| 1 <= j && j <= old(self).view().len(),
                        |j: nat| (j - 1) as nat,
                    ),
                );

                // 新規分を追加
                self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, new_head_pointsto);
                self.ghost_state@.ptrs = seq![new_head_ptr].add(self.ghost_state@.ptrs);

                old_head_ptr.next = Some(new_head_ptr);
            }
        }
    }

    pub fn pop_front(&mut self) -> (v: V) {
        let first_ptr = self.head.unwrap(); // tailはNoneでないことを前提とする
        
        let tracked first_pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(0);

        // into_inner https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html
        // Free the memory pointed to be perm and return the value that was previously there.
        // Requires the memory to be initialized. This consumes the PointsTo token,
        // since the user is giving up access to the memory by freeing it.
        let first_node = first_ptr.into_inner(Tracked(first_pointsto));

        let v = first_node.payload;

        match first_node.next {
            None => {
                // Popされたノードしか存在していない
                self.head = None;
            },
            Some(second_ptr) => {
                self.head = Some(second_ptr);
            }
        }

        return v;
    }
}

#[verifier::external]
fn main() {
    let mut sl = SinglyLinkedList::<u32>::new();

    sl.push_front(4);
    sl.push_front(3);

    println!("{}", sl.pop_front());
    println!("{}", sl.pop_front());
}

}