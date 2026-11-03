def _dead_leaf():
    return 0


def _cycle_a():
    return _cycle_b()


def _cycle_b():
    return _cycle_a()
