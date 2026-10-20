#!/bin/env python3

from typing import Self, TypeAlias
from collections import deque
from copy import deepcopy
import graphviz

class State:
    def __str__(self) -> str:
        return "State"

    def __hash__(self):
        # Use sth like powers construction to make the int unique
        return 0

    def __eq__(self, other: Self):
        return hash(self) == hash(other)

    def get_successors(self):
        return set()

class ImplicitTSystem:
    def __init__(self):
        self.init_states = []

    def add_init_state(self, state: State):
        self.init_states.append(state)
    
    def draw_state_graph(self) -> graphviz.Digraph:
        dot = graphviz.Digraph()

        states = self.get_states()
        print(states)
        for state in states:
            dot.node(str(state))
        ([dot.edge(str(state), str(succ), label)
                   for state in states
                   for label, succ in state.get_successors()])

        return dot

    def get_states(self) -> set[State]:
        states = set(self.init_states)
        unexpanded = deepcopy(self.init_states)

        while unexpanded:
            state = unexpanded.pop()
            successors = {s for l, s in state.get_successors()}
            unexpanded.extend(successors - states)
            for s in successors:
                seen = False
                for t in states:
                    if s == t:
                        seen = True
                        break
                if not seen:
                    states.add(s)

        return states


Clock: TypeAlias = int
# Constraint of form F: Region -> bool
# True means constraints are satisfied
ClockConst: TypeAlias = object
MaxConst: TypeAlias = dict[Clock, int]
Loc: TypeAlias = int
ClockReset: TypeAlias = list[Clock]
Label: TypeAlias = str

class Region:
    # Valuation val as {0: (1, True), 1: (2, False), 2: (2, False), 3: (0, False), 4: (1, True)}
    #     clock: (floor_part, is_integer)
    #     Out-of-bounds as clock: (max_const[clock], True)
    # order_f as deque({0, 4}, {2, 1}, {3}])
    # In case of elems with equal frac parts, order is sorted wrt. them
    def __init__(self, clocks: int, max_const: MaxConst, val=None, order_f=None):
        self.clocks = clocks
        self.max_const = max_const

        if val is None:
            assert (order_f is None), "Either none or all of val, order_f must be None"
            self.val = dict([(c, (0, True)) for c in range(clocks)])
            self.order_f = deque([set(range(clocks))])
        else:
            self.val = val
            assert (order_f is not None), "Either none or all of val, order_f must be None"
            self.order_f = order_f

    def __str__(self) -> str:
        string = " < ".join(map(
            lambda same: " = ".join(map(
                # TODO: Only print if nonzero
                lambda x: f"f(x_{x})", same
                )),
            self.order_f
            ))
        for x, (floor, is_int) in self.val.items():
            if is_int:
                string += f", x_{x}={floor}"
            elif floor < self.max_const[x]:
                string += f", {floor}<x_{x}<{floor+1}"
            else:
                string += f", {floor}<x_{x}"
        return string

    def __eq__(self, other):
        return self.clocks == other.clocks \
                and self.max_const == other.max_const \
                and self.val == other.val \
                and self.order_f == other.order_f

    # Returns first region acquired by non-self-loop delay
    def _delay_irreflective(self) -> Self:
        assert not all(map(lambda c:
                          self.val[c][0] >= self.max_const[c]
                          and not self.val[c][1],
                          range(self.clocks)))
        assert self.order_f

        delayed = Region(
                self.clocks,
                self.max_const,
                deepcopy(self.val),
                deepcopy(self.order_f)
                )

        max_frac = delayed.order_f.pop()

        # All max_frac have either zero or nonzero frac part
        assert max_frac
        for c in max_frac:
            floor, no_frac = delayed.val[c]
            break
        for c in max_frac:
            floor_, no_frac_ = delayed.val[c]
            assert no_frac_ == no_frac

        for c in list(max_frac):
            floor, no_frac = delayed.val[c]
            print(c, floor, no_frac)
            if no_frac:
                floor, no_frac = floor, False  # 2.0 -> 2.sth
                if floor >= self.max_const[c]:
                    # We get over bounds - no need to update anymore
                    max_frac.remove(c)
            elif floor >= self.max_const[c]:
                assert False, "Clock over bounds should never be inside order_f"
            else:
                floor, no_frac = floor+1, True     # 2.sth -> 3.0
            delayed.val[c] = (floor, no_frac)

        if max_frac:
            if no_frac:
                delayed.order_f.append(max_frac)
            else:
                delayed.order_f.appendleft(max_frac)

        return delayed

    def delay(self) -> list[Self]:
        print("Delaying")
        regions = []

        # Self-loop on all non-zero fractional or out of constraints
        if all(map(lambda val: not val[1], self.val.values())):
            regions.append(self)

        # Generate all clocks with delays
        delayed = self
        print("Pre-delay")
        print(delayed)
        print(delayed.val, self.max_const, delayed.order_f)
        while not all(map(lambda c:
                          delayed.val[c][0] >= self.max_const[c]
                          and not delayed.val[c][1],
                          range(self.clocks))):
            print("Delay step")
            delayed = delayed._delay_irreflective()
            print(delayed)
            print(delayed.val, self.max_const, delayed.order_f)
            regions.append(delayed)

        return regions

    def reset_clocks(self, clocks: list[Clock]) -> Self:
        if not clocks:
            return self
    
        clocks = deepcopy(clocks)
        values = deepcopy(self.val)
        for c in clocks:
            values[c] = (0, True)

        # To make things easier, add all clocks with 0-value to "reset"
        for c, v in values.items():
            floor, no_frac = v
            if no_frac and c not in clocks:
                clocks.append(c)

        order_f = deque()
        clocks = set(clocks)
        # Remove all 0-frac from other equality sets
        order_f.extend(filter(lambda x: x, map(lambda cs: cs - clocks, self.order_f)))
        # The resetted clocks (0-frac) are to be changed first
        order_f.append(clocks)

        return Region(
                self.clocks,
                self.max_const,
                values,
                order_f
                )


class TA(ImplicitTSystem):
    def __init__(
            self,
            locs: int,
            clocks: int,
            max_const: MaxConst,
            loc_const: dict[Loc, ClockConst],
            edges: list[tuple[Loc, Loc, Label, ClockConst, ClockReset]]
            ):
        super().__init__()
        self.locs = locs
        self.clocks = clocks
        self.max_const = max_const
        self.loc_const = loc_const
        self.edges = edges


class RGState(State):
    def __init__(self, ta: TA, loc, region=None):
        super().__init__()

        if region is None:
            region = Region(ta.clocks, ta.max_const)

        self.region = region
        self.loc = loc
        self.ta = ta

        assert self.is_valid()

    def __str__(self) -> str:
        return f"(s_{self.loc}, {self.region})"

    def __eq__(self, other) -> bool:
        return str(self) == str(other)
        return self.region == other.region \
                and self.loc == other.loc \
                and self.ta == other.ta

    def __hash__(self) -> int:
        return 0

    def get_successors(self) -> set[tuple[Label, Self]]:
        print("Getting successors")
        successors = set()
        
        # Delay successors
        for r in self.region.delay():
            rgstate = RGState(self.ta, self.loc, r)
            if rgstate.is_valid():
                print("Adding delay successor", self, '->', rgstate)
                print(self.region, "->", r)
                print(self.region.val, self.region.order_f, "->", r.val, r.order_f)
                successors.add(("d", rgstate))

        # Move successors
        for l1, l2, label, const, reset in self.ta.edges:
            if l1 == self.loc and const(self.region.val):
                region = self.region.reset_clocks(reset)
                rgstate = RGState(self.ta, l2, region)
                print("Adding move successor", self, "->", rgstate)
                print("Using:", l1, l2, const, reset)
                print(self.region, "->", region)
                print(self.region.val, self.region.order_f, "->", region.val, region.order_f)
                successors.add((label, rgstate))

        return successors

    def is_valid(self):
        if self.loc in self.ta.loc_const:
            return self.ta.loc_const(self.region)
        return True


if __name__ == "__main__":
    ta = TA(4, 2, {0: 1, 1: 1}, dict(),
            [
                (0, 1, 'a', lambda val: True, [0]),
                (1, 0, 'c', lambda val: val[0][0] >= 1, []),
                (1, 2, 'b', lambda val: val[0][0] < 1, [1]),
                (2, 3, 'c', lambda val: val[1][0] < 1 or (val[1][0]==1 and val[1][1]), []),
                (3, 1, 'c', lambda val: True, [0])
                ]
            )

    ta.add_init_state(a:=RGState(ta, 0))
    ta.add_init_state(b:=RGState(ta, 1))
    ta.add_init_state(c:=RGState(ta, 2))
    ta.add_init_state(d:=RGState(ta, 3))
    
    #print(b)
    #for label, b in b.get_successors():
    #    print(b)
    #    print(b.region.order_f)

    ta.draw_state_graph().render()
