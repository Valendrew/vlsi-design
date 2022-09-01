import pulp
import math
import numpy as np


def build_pulp_model(W: int, N: int, widths, heights) -> pulp.LpProblem:
    prob = pulp.LpProblem("vlsi", pulp.LpMinimize)

    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    l_up = int(sum(heights))

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pulp.LpInteger)
    prob += l, "Height of the plate"

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
        prob += coord_x[i] + widths[i] <= W, f"X-axis of {i}-th coordinate bound"
        prob += coord_y[i] + heights[i] <= l, f"Y-axis of {i}-th coordinate bound"

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
    prob += coord_x[max_circuit] == 0, "Max circuit in x-0"
    prob += coord_y[max_circuit] == 0, "Max circuit in y-0"

    return prob


def build_pulp_rotation_model(W: int, N: int, widths, heights) -> pulp.LpProblem:
    prob = pulp.LpProblem("vlsi-with-rotation", pulp.LpMinimize)

    # Lower and upper bounds for the height
    l_low = math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    l_up = int(sum([max(heights[i], widths[i]) for i in range(N)]))

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pulp.LpInteger)
    prob += l, "Height of the plate"

    # Coordinate variables
    set_N = range(N)
    c_wh_up = min(widths+heights)
    cx_up = int(W - c_wh_up)
    cy_up = int(l_up - c_wh_up)
    coord_x = pulp.LpVariable.dicts(
        "coord_x", indices=set_N, lowBound=0, upBound=cx_up, cat=pulp.LpInteger
    )
    coord_y = pulp.LpVariable.dicts(
        "coord_y", indices=set_N, lowBound=0, upBound=cy_up, cat=pulp.LpInteger
    )

    # Rotation variables
    rotation = pulp.LpVariable.dicts(
        "rot", indices=set_N, lowBound=0, upBound=1, cat=pulp.LpBinary
    )

    for i in set_N:
        if widths[i] == heights[i] or heights[i] > W:
            rotation[i] = 0

    # Boundary constraints
    for i in set_N:
        prob += (
            coord_x[i] + widths[i] * (1 - rotation[i]) + heights[i] * rotation[i] <= W,
            f"X-axis of {i}-th coordinate bound",
        )
        prob += (
            coord_y[i] + heights[i] * (1 - rotation[i]) + widths[i] * rotation[i] <= l,
            f"Y-axis of {i}-th coordinate bound",
        )

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
                """prob += coord_x[i] + widths[i] * (1 - rotation[i]) + heights[i] * rotation[i] <= coord_x[j] + (1 - delta[i][j][0]) * W
                prob += coord_x[j] + widths[j] * (1 - rotation[j]) + heights[j] * rotation[j] <= coord_x[i] + (1 - delta[j][i][0]) * W
                prob += (
                    coord_y[i] + heights[i] * (1 - rotation[i]) + widths[i] * rotation[i] <= coord_y[j] + (1 - delta[i][j][1]) * l_up
                )
                prob += (
                    coord_y[j] + heights[j] * (1 - rotation[j]) + widths[j] * rotation[j] <= coord_y[i] + (1 - delta[j][i][1]) * l_up
                )"""

                prob += (
                    coord_x[i]
                    + widths[i] * (1 - rotation[i])
                    + heights[i] * rotation[i]
                    <= coord_x[j]
                    + (delta[j][i][0] + delta[i][j][1] + delta[j][i][1]) * W
                )
                prob += (
                    coord_x[j]
                    + widths[j] * (1 - rotation[j])
                    + heights[j] * rotation[j]
                    <= coord_x[i]
                    + (delta[i][j][0] + delta[i][j][1] + delta[j][i][1]) * W
                )

                prob += (
                    coord_y[i]
                    + heights[i] * (1 - rotation[i])
                    + widths[i] * rotation[i]
                    <= coord_y[j]
                    + (delta[i][j][0] + delta[j][i][0] + delta[j][i][1]) * l_up
                )
                prob += (
                    coord_y[j]
                    + heights[j] * (1 - rotation[j])
                    + widths[j] * rotation[j]
                    <= coord_y[i]
                    + (delta[i][j][0] + delta[j][i][0] + delta[i][j][1]) * l_up
                )

                prob += (
                    delta[i][j][0] + delta[j][i][0] + delta[i][j][1] + delta[j][i][1]
                    == 1
                )

    max_circuit = np.argmax(np.asarray(widths) * np.asarray(heights))
    prob += coord_x[max_circuit] == 0, "Max circuit in x-0"
    prob += coord_y[max_circuit] == 0, "Max circuit in y-0"

    return prob
