use vstd::prelude::*;

verus! {

use vstd::cell::*;

pub struct ListLinkV<'a, T: 'a + ?Sized>(pub PCell<Option<&'a T>>);

impl<'a, T: ?Sized> ListLinkV<'a, T> {
    pub const fn empty() -> (res: (Self, Tracked<PointsTo<Option<&'a T>>>))
        ensures
            res.0.0.id() == res.1@.id(),
            res.1@.is_init(),
            match res.1@.value() {
                Option::Some(_) => false,
                Option::None => true,
            },
    {
        let (cell, points_to) = PCell::<Option<&'a T>>::new(None);
        (ListLinkV(cell), points_to)
    }
}

pub trait ListNodeV<'a, T: ?Sized> {
    fn next(&'a self, next_points_to: Tracked<&PointsTo<Option<&'a T>>>) -> (res: &'a ListLinkV<
        'a,
        T,
    >)
        ensures
            res.0.id() == next_points_to@.id(),
    ;
}

pub struct ListV<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub head: ListLinkV<'a, T>,
}

pub tracked struct GhostState<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub ghost cells: Seq<&'a PCell<Option<&'a T>>>,
    pub tracked points_to_map: Map<nat, PointsTo<Option<&'a T>>>,
}

pub struct ListIteratorV<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub cur: Option<&'a T>,
    pub index: Ghost<nat>,
}

pub open spec fn well_formed_node<'a, T: 'a + ?Sized + ListNodeV<'a, T>>(
    ghost_state: &Tracked<GhostState<'a, T>>,
    i: nat,
) -> bool {
    &&& ghost_state@.points_to_map.dom().contains(i)
    &&& ghost_state@.points_to_map[i].is_init()
    &&& ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id()
}

impl<'a, T: ?Sized + ListNodeV<'a, T>> ListIteratorV<'a, T> {
    pub closed spec fn valid_list_iterator(
        &self,
        ghost_state: &Tracked<GhostState<'a, T>>,
    ) -> bool {
        &&& ghost_state@.cells.len() > self.index@
        &&& forall|i: nat|
            self.index@ <= i < ghost_state@.cells.len()
                ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                == ghost_state@.cells[i as int].id()
        &&& forall|i: nat|
            self.index@ <= i < (ghost_state@.cells.len() - 1) as nat
                ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                Option::Some(_) => true,
                Option::None => false,
            }
        &&& match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
            Option::Some(_) => false,
            Option::None => true,
        }
        &&& self.cur == ghost_state@.points_to_map[self.index@].value()
    }

    pub fn new(l: &'a ListV<'a, T>, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Self)
        requires
            ghost_state@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            forall|i: nat|
                0 <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            ghost_state@.cells[0].id() == l.head.0.id(),
        ensures
            res.index@ == 0,
            res.valid_list_iterator(ghost_state),
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(0);
        let cur = *l.head.0.borrow(Tracked(points_to));
        ListIteratorV { cur, index: Ghost(0) }
    }




    // pub broadcast proof fn lemma_temp(&mut self, ghost_state: &Tracked<GhostState<'a, T>>)
    // pub closed spec fn lemma_temp(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> bool
    //     requires
    //     // p.aligned(), v.aligned(), p.modulo == v.modulo,
    //     ensures
    //     // (#[trigger] p.add(v)).aligned(),
    //     // p.add(v).modulo == lib::same_or_arbitrary(p.modulo, v.modulo),
    // {
    //         &&& ghost_state@.points_to_map.dom().contains(self.index@)
    //         &&& ghost_state@.points_to_map[self.index@].is_init()
    //         &&& ghost_state@.points_to_map[self.index@].id()
    //             == ghost_state@.cells[self.index@ as int].id()
    // }

    // pub closed spec fn lemma_temp2(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> bool
    // {
    //     true
    // }

    pub fn next(&mut self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
            old(self).valid_list_iterator(ghost_state),
        ensures
            self.valid_list_iterator(ghost_state),
            res == ghost_state@.points_to_map[old(self).index@].value(),
            match res {
                Option::Some(_) => old(self).index@ + 1 < ghost_state@.cells.len() && self.index@
                    + 1 <= ghost_state@.cells.len() && self.index@ == old(self).index@ + 1,
                Option::None => old(self).index@ + 1 == ghost_state@.cells.len() && self.index@ + 1
                    == ghost_state@.cells.len() && self.index@ == old(self).index@,
            },
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(self.index@));
            assert(ghost_state@.points_to_map[self.index@].is_init());
            assert(ghost_state@.points_to_map[self.index@].id()
                == ghost_state@.cells[self.index@ as int].id());
            // self.lemma_temp(ghost_state);
        }
        match self.cur {
            Some(res) => {
                proof {
                    assert(self.index@ < (ghost_state@.cells.len() - 1) as nat);
                    self.index@ = self.index@ + 1;
                    assert(ghost_state@.points_to_map.dom().contains(self.index@));
                    assert(ghost_state@.points_to_map[self.index@].is_init());
                    assert(ghost_state@.points_to_map[self.index@].id()
                        == ghost_state@.cells[self.index@ as int].id());
                }

                let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(
                    self.index@,
                );
                let next = res.next(Tracked(points_to));
                self.cur = *next.0.borrow(Tracked(points_to));
                Some(res)
            },
            None => {
                proof {
                    assert(self.index@ + 1 == ghost_state@.cells.len());
                    assert(ghost_state@.points_to_map.dom().contains(self.index@));
                    assert(ghost_state@.points_to_map[self.index@].is_init());
                    assert(ghost_state@.points_to_map[self.index@].id()
                        == ghost_state@.cells[self.index@ as int].id());
                }

                None
            },
        }
    }

    pub fn last(&mut self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
            old(self).valid_list_iterator(ghost_state),
        ensures
            ghost_state@.cells.len() == self.index@ + 1,
            self.cur == ghost_state@.points_to_map[self.index@].value(),
            match res {
                Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                    (self.index@ - 1) as nat,
                ) && res == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                Option::None => old(self).index@ + 1 == ghost_state@.cells.len(),
            },
    {
        let mut last = None;
        assert(old(self).index@ == self.index@);
        loop
            invariant_except_break
                self.valid_list_iterator(ghost_state),
                match last {
                    Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                        (self.index@ - 1) as nat,
                    ) && last == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                    Option::None => self.index@ == old(self).index@,
                },
            ensures
                ghost_state@.cells.len() == self.index@ + 1,
                self.cur == ghost_state@.points_to_map[self.index@].value(),
                match last {
                    Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                        (self.index@ - 1) as nat,
                    ) && last == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                    Option::None => old(self).index@ + 1 == ghost_state@.cells.len(),
                },
        {
            let cur = self.next(ghost_state);
            if cur.is_none() {
                proof {
                    assert(match last {
                        Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                            (self.index@ - 1) as nat,
                        ) && last == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                        Option::None => old(self).index@ + 1 == ghost_state@.cells.len(),
                    });
                }
                break ;
            } else {
                proof {
                    assert(match cur {
                        Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                            (self.index@ - 1) as nat,
                        ) && cur == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                        Option::None => false,
                    });
                }
                last = cur;
            }
        }
        last
    }
}

impl<'a, T: ?Sized + ListNodeV<'a, T>> ListV<'a, T> {
    // https://github.com/verus-lang/verus/blob/4e32f3ab2b23b28194857126330662642f7d5e2e/source/rust_verify/example/doubly_linked.rs#L56
    // https://github.com/microsoft/verismo/blob/a120c4576b4969d4575f34b266128c9f7c823fd2/source/verismo/src/linkedlist/mod.rs#L143
    pub open spec fn well_formed_list(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> bool {
        // list length = cells length - 1 (the last cell contains None)
        &&& ghost_state@.cells.len() >= 1
        &&& forall|i: nat|
            0 <= i < ghost_state@.cells.len() ==> well_formed_node(
                ghost_state,
                i,
            )
        // every cell except the last one should not be None
        &&& forall|i: nat|
            0 <= i < (ghost_state@.cells.len() - 1) as nat
                ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                Option::Some(_) => true,
                Option::None => false,
            }
            // the last cell contains None
        &&& match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
            Option::Some(_) => false,
            Option::None => true,
        }
        &&& ghost_state@.points_to_map.dom().contains((ghost_state@.cells.len() - 1) as nat)
        &&& ghost_state@.cells[0].id() == self.head.0.id()
        &&& forall|i: nat|
            0 <= i < ghost_state@.cells.len() ==>
            #[trigger] ghost_state@.points_to_map.dom().contains(i)
        // &&& forall|i: nat|
        //     0 <= i < ghost_state@.cells.len() ==>
        //     #[trigger] ghost_state@.points_to_map[i].is_init()
    //     &&& forall|i: nat|
    //         0 <= i < ghost_state@.cells.len() ==>
    //         #[trigger] ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id()
    }

    pub const fn new() -> (res: (Self, Tracked<GhostState<'a, T>>))
        ensures
    // list length = cells length - 1 (last cell contains None)

            res.1@.cells.len() == 1,
            well_formed_node(&res.1, 0),
            res.0.well_formed_list(&res.1),
    {
        let (list_link, Tracked(points_to)) = ListLinkV::<T>::empty();
        let mut ghost_state = Tracked(
            GhostState { cells: Seq::empty(), points_to_map: Map::tracked_empty() },
        );

        proof {
            ghost_state.borrow_mut().cells = ghost_state@.cells.push(&list_link.0);
            ghost_state.borrow_mut().points_to_map.tracked_insert(0, points_to);
        }

        let list = ListV { head: list_link };

        (list, ghost_state)
    }

    pub fn head(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
    // list length = cells length - 1 (last cell contains None)

            ghost_state@.cells.len() >= 1,
            well_formed_node(ghost_state, 0),
            ghost_state@.cells[0].id() == self.head.0.id(),
        ensures
            ghost_state@.points_to_map[0].value() == res,
    {
        let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(0);
        *self.head.0.borrow(Tracked(points_to))
    }

    pub fn push_head(
        &self,
        node: &'a T,
        next_points_to: Tracked<PointsTo<Option<&'a T>>>,
        ghost_state: &mut Tracked<GhostState<'a, T>>,
    )
        requires
    // VERUS-TODO manually inlined due to errors (`a mutable reference is expected here`) when using `self.well_formed_list(old(ghost_state))`.
    // list length = cells length - 1 (last cell contains None)

            self.well_formed_list(old(ghost_state)),
            // old(ghost_state)@.cells.len() >= 1,
            // forall|i: nat|
            //     0 <= i < old(ghost_state)@.cells.len()
            //     ==> #[trigger] old(ghost_state)@.points_to_map.dom().contains(i)
            //     && old(ghost_state)@.points_to_map[i].is_init() // every node is init in ghost
            //     && old(ghost_state)@.points_to_map[i].id() == old(ghost_state)@.cells[i as int].id(),
            // // every cell except the last one should not be None
            // forall|i: nat|
            //     0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> match #[trigger] old(
            //         ghost_state,
            //     )@.points_to_map[i].value() {
            //         Option::Some(_) => true,
            //         Option::None => false,
            //     },
            // // the last cell contains None
            // match old(ghost_state)@.points_to_map[(old(ghost_state)@.cells.len()
            //     - 1) as nat].value() {
            //     Option::Some(_) => false,
            //     Option::None => true,
            // },
            // old(ghost_state)@.cells[0].id() == self.head.0.id(),
            next_points_to@.is_init(),
        ensures
            old(ghost_state)@.cells.len() + 1 == ghost_state@.cells.len(),
            self.well_formed_list(ghost_state),
            // not sure why this is needed as it should be included in well_formed_list
            // but removing it will cause subsequent calls not verified

            // original
            // forall|i: nat|
            //     0 <= i < ghost_state@.cells.len()
            //         ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
            //         && ghost_state@.points_to_map[i].is_init(),
            //         && ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id(),


            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init()
                    && ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id(),


            forall|i: nat| // separate &&s into individual properties
                0 <= i < ghost_state@.cells.len() ==>
                    #[trigger] ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id(),

            // assert binary search, add asserts to find why it is not holding, what part is not holding and why
            // keep asking if it is true
            // this will let you find what the solver does and does not know
            ghost_state@.points_to_map[0].value().unwrap() == node,
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value().unwrap() == ghost_state@.points_to_map[i
                    + 1].value().unwrap(),
    {
        proof {
            // assert( forall|i: nat|
            //     0 <= i < old(ghost_state)@.cells.len()
            //     ==> #[trigger] old(ghost_state)@.points_to_map.dom().contains(i)
            //     && old(ghost_state)@.points_to_map[i].is_init());

            // assert(forall|i: nat|
            //     0 <= i < ghost_state@.cells.len()
            //         ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
            //         && ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id());
            // assert(forall|i: nat|
            //     0 <= i < ghost_state@.cells.len()
            //         ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
            //          && ghost_state@.points_to_map[i].is_init());
        //     assert(
        //         forall|i: nat| 0 <= i < ghost_state@.cells.len() ==>
        // ghost_state@.points_to_map.dom().contains(i)
        //     );
        //     assert(ghost_state@.cells.len() >= 1);
            assert(ghost_state == old(ghost_state));
            assert(ghost_state@.points_to_map.dom().contains((ghost_state@.cells.len() - 1) as nat));
            assert(ghost_state@.cells.len() - 1 >= 0);
            assert(forall|i: nat|
                0 <= i < ghost_state@.cells.len() ==> well_formed_node(
                    ghost_state,
                    i,
                ));
            assert(forall|i: nat|
                0 <= i < ghost_state@.cells.len() && well_formed_node(ghost_state, i) ==> #[trigger] ghost_state@.points_to_map.dom().contains(i));
            assert(ghost_state@.points_to_map.dom().contains(0));
            // assert(ghost_state@.cells[0].id() == self.head.0.id());
            assert(forall|i: nat|
                0 <= i < ghost_state@.cells.len() && well_formed_node(ghost_state, i) ==> #[trigger] ghost_state@.points_to_map[i].is_init());
            assert(ghost_state@.points_to_map[0].is_init());
            assert(forall|i: nat|
                0 <= i < ghost_state@.cells.len() && well_formed_node(ghost_state, i) ==> #[trigger] ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id());
            assert(ghost_state@.points_to_map[0]@.pcell == self.head.0.id());
        }
        // assert/assume each assumption in a proof block and move it around
        let tracked mut head_points_to = ghost_state.borrow_mut().points_to_map.tracked_remove(0);
        proof {
            assert(head_points_to.is_init());
            assert(self.head.0.id() == head_points_to@.pcell);
            // assert(head_points_to.id() == ghost_state@.cells[0].id());
        }
        let old_head_value = *self.head.0.borrow(Tracked(&head_points_to));
        let tracked mut next_ptr = next_points_to.get();
        let next_node = node.next(Tracked(&next_ptr));
        next_node.0.write(Tracked(&mut next_ptr), old_head_value);
        self.head.0.write(Tracked(&mut head_points_to), Some(node));
        let cell = &next_node.0;

        proof {
            ghost_state.borrow_mut().cells = ghost_state@.cells.insert(1, cell);
            // it might be okay that there is a failure early on. Postcondition does not need to hold at *any* time in the function
            // something in this proof is not restablushgin postcond

            // understand this proof block, try putting assumes around


            // push this code so that eric can look at it this weekend.
            // need to finish debugging and isolating before then
            // comment the code and what it is supposed to be doing.
            // TODO: need to isolate the failure. how to ignore the other failing functions??????
            ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                Map::<nat, nat>::new(
                    |j: nat| 2 <= j && j < ghost_state@.cells.len(),
                    |j: nat| (j - 1) as nat,
                ),
            );
            ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
            ghost_state.borrow_mut().points_to_map.tracked_insert(1, next_ptr);
            assert forall|i: nat| 2 <= i < ghost_state@.cells.len() implies well_formed_node(
                ghost_state,
                i,
            ) by {
                assert(1 <= i - 1 < old(ghost_state)@.cells.len());
                assert(old(ghost_state)@.cells[i - 1] == ghost_state@.cells[i as int]);
                assert(old(ghost_state)@.points_to_map.dom().contains((i - 1) as nat)
                    == ghost_state@.points_to_map.dom().contains(i));
                assert(old(ghost_state)@.points_to_map[(i - 1) as nat]
                    == ghost_state@.points_to_map[i]);
            }
            assert forall|i: nat|
                1 <= i < (old(ghost_state)@.cells.len()
                    - 1) implies #[trigger] ghost_state@.points_to_map.dom().contains(i + 1)
                && ghost_state@.points_to_map[i + 1].is_init() by {
                assert(old(ghost_state)@.points_to_map.dom().contains(i)
                    == ghost_state@.points_to_map.dom().contains(i + 1));
                assert(old(ghost_state)@.points_to_map[i] == ghost_state@.points_to_map[i + 1]);
            }
            // assert forall|i: nat|
            //     0 <= i < ghost_state@.cells.len()
            //         ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
            //         && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
            //         == ghost_state@.cells[i as int].id() by {
            //         }

        }
    }

    pub fn push_tail(
        &'a self,
        node: &'a T,
        next_points_to: Tracked<PointsTo<Option<&'a T>>>,
        ghost_state: &mut Tracked<GhostState<'a, T>>,
    )
        requires
    // VERUS-TODO manually inlined due to errors (`a mutable reference is expected here`) when using `self.well_formed_list(old(ghost_state))`.
    // list length = cells length - 1 (last cell contains None)

            old(ghost_state)@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < old(ghost_state)@.cells.len() ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map.dom().contains(i) && old(ghost_state)@.points_to_map[i].is_init()
                    && old(ghost_state)@.points_to_map[i].id() == old(
                    ghost_state,
                )@.cells[i as int].id(),
            // every cell except the last one should not be None
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> match #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            // the last cell contains None
            match old(ghost_state)@.points_to_map[(old(ghost_state)@.cells.len()
                - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(ghost_state)@.cells[0].id() == self.head.0.id(),
            next_points_to@.is_init(),
        ensures
            old(ghost_state)@.cells.len() + 1 == ghost_state@.cells.len(),
            self.well_formed_list(ghost_state),
            // not sure why this is needed as it should be included in well_formed_list
            // but removing it will cause subsequent calls not verified
            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            ghost_state@.points_to_map[(ghost_state@.cells.len() - 2) as nat].value().unwrap()
                == node,
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value().unwrap()
                    == ghost_state@.points_to_map[i].value().unwrap(),
    {
        proof {
            assert(forall|i: nat|
            0 <= i < ghost_state@.cells.len() ==> well_formed_node(
                ghost_state,
                i,
            ));
        }
        let tracked mut next_ptr = next_points_to.get();
        let next_node = node.next(Tracked(&next_ptr));
        next_node.0.write(Tracked(&mut next_ptr), None);
        proof {
            assert(ghost_state@.points_to_map.dom().contains(
                (ghost_state@.cells.len() - 1) as nat,
            ));
        }
        let last = {
            let mut iter = self.iter(ghost_state);
            iter.last(ghost_state)
        };
        match last {
            Some(last) => {
                let tracked mut tail_points_to =
                    ghost_state.borrow_mut().points_to_map.tracked_remove(
                    (ghost_state@.cells.len() - 1) as nat,
                );
                last.next(Tracked(&tail_points_to)).0.write(
                    Tracked(&mut tail_points_to),
                    Some(node),
                );
                let cell = &next_node.0;

                proof {
                    ghost_state.borrow_mut().cells = ghost_state@.cells.push(cell);
                    ghost_state.borrow_mut().points_to_map.tracked_insert(
                        (ghost_state@.cells.len() - 2) as nat,
                        tail_points_to,
                    );
                    ghost_state.borrow_mut().points_to_map.tracked_insert(
                        (ghost_state@.cells.len() - 1) as nat,
                        next_ptr,
                    );
                    assert(ghost_state@.cells.len() >= 1);
                    assert(well_formed_node(ghost_state, (ghost_state@.cells.len() - 2) as nat));
        assert(forall|i: nat|
            0 <= i < ghost_state@.cells.len() ==>
            #[trigger] ghost_state@.points_to_map.dom().contains(i)
            && ghost_state@.points_to_map[i].is_init()
            && ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id()
        );
        // assert( forall|i: nat|
        //     0 <= i < ghost_state@.cells.len()  - 2==>
        //     #[trigger] ghost_state@.points_to_map[i].is_init());
        // &&& forall|i: nat|
        //     0 <= i < ghost_state@.cells.len() ==>
        //     #[trigger] ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id());
                    assert(forall|i: nat|
                        0 <= i < ghost_state@.cells.len() ==> well_formed_node(
                            ghost_state,
                            i,
                        ) );
                    // need to reestablisht that the list is well formed after mutating it. Prove that the last item in the list preserves the list properties
                    assert(self.well_formed_list(ghost_state));
                }
            },
            None => self.push_head(node, Tracked(next_ptr), ghost_state),
        }
    }

    pub fn pop_head(&self, ghost_state: &mut Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
    // VERUS-TODO manually inlined due to errors (`a mutable reference is expected here`) when using `self.well_formed_list(old(ghost_state))`.
    // list length = cells length - 1 (last cell contains None)
            self.well_formed_list(old(ghost_state)),
            old(ghost_state)@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < old(ghost_state)@.cells.len() ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map.dom().contains(i) && old(ghost_state)@.points_to_map[i].is_init()
                    && old(ghost_state)@.points_to_map[i].id() == old(
                    ghost_state,
                )@.cells[i as int].id(),
            // every cell except the last one should not be None
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat && old(ghost_state)@.points_to_map[i].is_init() ==> match #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            // the last cell contains None
            match old(ghost_state)@.points_to_map[(old(ghost_state)@.cells.len()
                - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(ghost_state)@.cells[0].id() == self.head.0.id(),
        ensures
            self.well_formed_list(ghost_state),
            // not sure why this is needed as it should be included in well_formed_list
            // but removing it will cause subsequent calls not verified
            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id()
                ,
            if old(ghost_state)@.cells.len() == 1 {
                old(ghost_state)@.cells.len() == ghost_state@.cells.len()
            } else {
                old(ghost_state)@.cells.len() - 1 == ghost_state@.cells.len() && old(
                    ghost_state,
                )@.points_to_map[0].value() == res && forall|i: nat|
                    1 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> #[trigger] old(
                        ghost_state,
                    )@.points_to_map[i].value().unwrap() == ghost_state@.points_to_map[(i
                        - 1) as nat].value().unwrap()
            },
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        let tracked mut head_points_to = ghost_state.borrow_mut().points_to_map.tracked_remove(0);
        let remove = *self.head.0.borrow(Tracked(&head_points_to));
        match remove {
            Some(node) => {
                proof {
                    assert(ghost_state@.cells.len() > 1);
                    assert(ghost_state@.points_to_map.dom().contains(1));
                }

                {
                    let tracked next_points_to = ghost_state.borrow().points_to_map.tracked_borrow(
                        1,
                    );
                    self.head.0.write(
                        Tracked(&mut head_points_to),
                        *node.next(Tracked(next_points_to)).0.borrow(Tracked(next_points_to)),
                    );
                }

                proof {
                    ghost_state.borrow_mut().cells = ghost_state@.cells.remove(1);
                    ghost_state.borrow_mut().points_to_map.tracked_remove(1);
                    ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |j: nat| 1 <= j && j < ghost_state@.cells.len(),
                            |j: nat| (j + 1) as nat,
                        ),
                    );
                    ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                    assert forall|i: nat|
                        1 <= i < ghost_state@.cells.len() implies well_formed_node(
                        ghost_state,
                        i,
                    ) by {
                        assert (1 <= i + 1 < old(ghost_state)@.cells.len());
                        assert(old(ghost_state)@.cells[(i + 1) as int]
                            == ghost_state@.cells[i as int]);
                        assert(old(ghost_state)@.points_to_map.dom().contains((i + 1) as nat)
                            == ghost_state@.points_to_map.dom().contains(i));
                        assert(old(ghost_state)@.points_to_map[(i + 1) as nat]
                            == ghost_state@.points_to_map[i]);
                    }
                    assert(forall|i: nat|
                        0 <= i < ghost_state@.cells.len() && well_formed_node(ghost_state, i) ==> #[trigger] ghost_state@.points_to_map[i].is_init());
                    assert(forall|i: nat|
                    0 <= i < ghost_state@.cells.len()
                        ==> #[trigger] ghost_state@.points_to_map[i].is_init());
                        assert(forall|i: nat|
                            0 <= i < ghost_state@.cells.len() && well_formed_node(ghost_state, i) ==> #[trigger] ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id());
                        // == ghost_state@.cells[i as int].id());
                }
            },
            None => {
                proof {
                    assert(ghost_state@.cells.len() == 1);
                }

                self.head.0.write(Tracked(&mut head_points_to), None);

                proof {
                    ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                }
            },
        }
        remove
    }

    pub fn iter(&'a self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: ListIteratorV<'a, T>)
        requires
    // list length = cells length - 1 (last cell contains None)

            ghost_state@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            // every cell except the last one should not be None
            forall|i: nat|
                0 <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            // the last cell contains None
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            ghost_state@.cells[0].id() == self.head.0.id(),
        ensures
            res.cur == ghost_state@.points_to_map[0].value(),
            res.index@ == 0,
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        ListIteratorV::<T>::new(self, ghost_state)
    }
}

// example of ListNodeV containing i32
pub struct I32Node<'a> {
    pub value: i32,
    pub next: Option<ListLinkV<'a, I32Node<'a>>>,
}

impl<'a> I32Node<'a> {
    pub fn new(value: i32) -> (res: (I32Node<'a>, Tracked<PointsTo<Option<&'a I32Node<'a>>>>))
        ensures
            match res.0.next {
                Option::Some(n) => n.0.id() == res.1@.id(),
                Option::None => false,
            },
            res.1@.is_init(),
            res.0.value == value,
    {
        let (list_link, tracked_points_to) = ListLinkV::<I32Node<'a>>::empty();
        (I32Node { value, next: Some(list_link) }, tracked_points_to)
    }
}

#[verifier::external]
impl<'a> ListNodeV<'a, I32Node<'a>> for I32Node<'a> {
    fn next(&'a self, next_points_to: Tracked<&PointsTo<Option<&'a I32Node<'a>>>>) -> (res:
        &'a ListLinkV<'a, I32Node<'a>>) {
        match &self.next {
            Some(next) => { next },
            None => { unreachable!() },
        }
    }
}

fn main() {
    // example: push_head
    {
        let (mut list, mut state) = ListV::<I32Node>::new();
        let (a, a_pt) = I32Node::new(1);
        list.push_head(&a, a_pt, &mut state);
        let mut it = list.iter(&state);
        let next_1 = it.next(&state);
        assert(next_1.is_some());
        assert(next_1.unwrap().value == 1);
        let next_2 = it.next(&state);
        assert(next_2.is_none());
    }

    // example: push_tail
    {
        let (mut list, mut state) = ListV::<I32Node>::new();
        let (a, a_pt) = I32Node::new(1);
        list.push_tail(&a, a_pt, &mut state);
        let mut it = list.iter(&state);
        let next_1 = it.next(&state);
        assert(next_1.is_some());
        assert(next_1.unwrap().value == 1);
        let next_2 = it.next(&state);
        assert(next_2.is_none());
    }

    // example: push and pop
    {
        let (mut list, mut state) = ListV::<I32Node>::new();
        let (a, a_pt) = I32Node::new(1);
        let (b, b_pt) = I32Node::new(2);
        list.push_head(&a, a_pt, &mut state);
        list.push_tail(&b, b_pt, &mut state);
        list.pop_head(&mut state);
        let mut it = list.iter(&state);
        let next_1 = it.next(&state);
        assert(next_1.is_some());
        assert(next_1.unwrap().value == 2);
        let next_2 = it.next(&state);
        assert(next_2.is_none());
    }

    // example: empty list
    {
        let (mut list, mut state) = ListV::<I32Node>::new();
        let (a, a_pt) = I32Node::new(1);
        let (b, b_pt) = I32Node::new(2);
        list.push_tail(&b, b_pt, &mut state);
        list.push_head(&a, a_pt, &mut state);
        list.pop_head(&mut state);
        list.pop_head(&mut state);
        let mut it = list.iter(&state);
        let next_1 = it.next(&state);
        assert(next_1.is_none());
    }

    // example: iterator
    {
        let (mut list, mut state) = ListV::<I32Node>::new();
        let (a, a_pt) = I32Node::new(1);
        let (b, b_pt) = I32Node::new(2);
        let (c, c_pt) = I32Node::new(3);
        list.push_head(&a, a_pt, &mut state);
        list.push_tail(&b, b_pt, &mut state);
        list.push_head(&c, c_pt, &mut state);
        let mut it = list.iter(&state);
        let next_1 = it.next(&state);
        assert(next_1.is_some());
        assert(next_1.unwrap().value == 3);
        let next_2 = it.next(&state);
        assert(next_2.is_some());
        assert(next_2.unwrap().value == 1);
        let next_3 = it.next(&state);
        assert(next_3.is_some());
        assert(next_3.unwrap().value == 2);
        let next_4 = it.next(&state);
        assert(next_4.is_none());
        let mut it2 = list.iter(&state);
        let last = it2.last(&state);
        assert(last.is_some());
        assert(last.unwrap().value == 2);
    }
}

} // verus!
