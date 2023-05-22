#!/usr/bin/env python3

from sys import argv
import spot


def verify(curr: int, next: int, model_file: str) -> bool:
    aut = spot.automaton(model_file)
    for state in range(aut.num_states()):
        for t in aut.out(state):
            if int(t.src) == curr and int(t.dst) == next:
                return True
    return False


def main(args: list):
    assert len(args) == 3  # pass trace file and model file

    with open(args[1], "r") as trace_file:
        trace = trace_file.readlines()[0].strip()
    model_file = args[2]

    counters = [0, 0]
    curr = int(trace[0])
    assert curr == 0  # first is push
    counters[curr] += 1

    for state in trace[1:]:
        state = int(state)
        assert state in (0, 1)
        counters[state] += 1
        assert verify(curr, state, model_file)
        curr = state

    assert curr == 1  # last is pop
    assert counters[0] == counters[1]  # equal number of push and pop

    print("correct")


if __name__ == "__main__":
    main(argv)
