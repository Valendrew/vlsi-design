import pulp
import math
import numpy as np


def build_pulp_model(W: int, N: int, widths, heights):
    prob = pulp.LpProblem("vlsi", pulp.LpMinimize)

    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    l_up = int(sum(heights))

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pulp.LpInteger)
    prob += l

    # Coordinate variables
    set_N = range(N)
    cx_up = int(W - min(widths))
    cy_up = int(l_up - min(heights))
    coord_x = pulp.LpVariable.dicts(
        "coord_x", indices=set_N, lowBound=0, upBound=cx_up, cat=pulp.LpInteger
    )
    coord_y = pulp.LpVariable.dicts(
        "coord_y", indices=set_N, lowBound=0, upBound=cy_up, cat=pulp.LpInteger
    )

    # Boundary constraints
    for i in set_N:
        prob += coord_x[i] + widths[i] <= W
        prob += coord_y[i] + heights[i] <= l

    # Booleans for OR condition
    set_C = range(2)
    delta = pulp.LpVariable.dicts(
        "delta",
        indices=(set_N, set_N, set_C),
        cat=pulp.LpBinary,
        lowBound=0,
        upBound=1,
    )

    # Non-Overlap constraints, at least one needs to be satisfied
    for i in set_N:
        for j in set_N:
            if i < j:
                """prob += coord_x[i] + widths[i] <= coord_x[j] + (1 - delta[i][j][0]) * W
                prob += coord_x[j] + widths[j] <= coord_x[i] + (1 - delta[j][i][0]) * W
                prob += (
                    coord_y[i] + heights[i] <= coord_y[j] + (1 - delta[i][j][1]) * l_up
                )
                prob += (
                    coord_y[j] + heights[j] <= coord_y[i] + (1 - delta[j][i][1]) * l_up
                )"""

                prob += (
                    coord_x[i] + widths[i]
                    <= coord_x[j]
                    + (delta[j][i][0] + delta[i][j][1] + delta[j][i][1]) * W
                )
                prob += (
                    coord_x[j] + widths[j]
                    <= coord_x[i]
                    + (delta[i][j][0] + delta[i][j][1] + delta[j][i][1]) * W
                )

                prob += (
                    coord_y[i] + heights[i]
                    <= coord_y[j]
                    + (delta[i][j][0] + delta[j][i][0] + delta[j][i][1]) * l_up
                )
                prob += (
                    coord_y[j] + heights[j]
                    <= coord_y[i]
                    + (delta[i][j][0] + delta[j][i][0] + delta[i][j][1]) * l_up
                )

                prob += (
                    delta[i][j][0] + delta[j][i][0] + delta[i][j][1] + delta[j][i][1]
                    == 1
                )

    max_circuit = np.argmax(np.asarray(widths) * np.asarray(heights))
    prob += coord_x[max_circuit] == 0
    prob += coord_y[max_circuit] == 0

    return prob


def build__rotation_pulp_model(W: int, N: int, widths, heights):
    # LpVariable() for new variables
    # LpProblem() for new problems
    prob = pulp.LpProblem("vlsi", pulp.LpMinimize)

    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    l_up = int(sum(heights))

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pulp.LpInteger)
    prob += l

    # Coordinate variables
    set_N = range(N)
    cx_up = int(W - min(widths))
    cy_up = int(l_up - min(heights))
    coord_x = pulp.LpVariable.dicts(
        "coord_x", indices=set_N, lowBound=0, upBound=cx_up, cat=pulp.LpInteger
    )
    coord_y = pulp.LpVariable.dicts(
        "coord_y", indices=set_N, lowBound=0, upBound=cy_up, cat=pulp.LpInteger
    )

    # Boundary constraints
    for i in set_N:
        prob += coord_x[i] + widths[i] <= W
        prob += coord_y[i] + heights[i] <= l

    # Booleans for OR condition
    set_C = range(2)
    delta = pulp.LpVariable.dicts(
        "delta",
        indices=(set_N, set_N, set_C),
        cat=pulp.LpBinary,
        lowBound=0,
        upBound=1,
    )

    # Non-Overlap constraints, at least one needs to be satisfied
    for i in set_N:
        for j in set_N:
            if i < j:
                """prob += coord_x[i] + widths[i] <= coord_x[j] + (1 - delta[i][j][0]) * W
                prob += coord_x[j] + widths[j] <= coord_x[i] + (1 - delta[j][i][0]) * W
                prob += (
                    coord_y[i] + heights[i] <= coord_y[j] + (1 - delta[i][j][1]) * l_up
                )
                prob += (
                    coord_y[j] + heights[j] <= coord_y[i] + (1 - delta[j][i][1]) * l_up
                )"""

                prob += (
                    coord_x[i] + widths[i]
                    <= coord_x[j]
                    + (delta[j][i][0] + delta[i][j][1] + delta[j][i][1]) * W
                )
                prob += (
                    coord_x[j] + widths[j]
                    <= coord_x[i]
                    + (delta[i][j][0] + delta[i][j][1] + delta[j][i][1]) * W
                )

                prob += (
                    coord_y[i] + heights[i]
                    <= coord_y[j]
                    + (delta[i][j][0] + delta[j][i][0] + delta[j][i][1]) * l_up
                )
                prob += (
                    coord_y[j] + heights[j]
                    <= coord_y[i]
                    + (delta[i][j][0] + delta[j][i][0] + delta[i][j][1]) * l_up
                )

                prob += (
                    delta[i][j][0] + delta[j][i][0] + delta[i][j][1] + delta[j][i][1]
                    == 1
                )

    max_circuit = np.argmax(np.asarray(widths) * np.asarray(heights))
    prob += coord_x[max_circuit] == 0
    prob += coord_y[max_circuit] == 0

    return prob
