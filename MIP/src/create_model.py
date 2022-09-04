from typing import List, Union
import pulp
import math
import numpy as np
import time


def build_positions_model(
    W: int, N: int, widths, heights
) -> Union[pulp.LpProblem, List[int]]:
    prob = pulp.LpProblem("vlsi", pulp.LpMinimize)

    # Lower and upper bounds for the height
    l_bound = max(
        max(heights), math.ceil(sum([widths[i] * heights[i] for i in range(N)]) / W)
    )

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_bound, upBound=l_bound, cat=pulp.LpInteger)
    prob += l, "Height of the plate"

    # Coordinate variables
    set_I = range(N)
    s_time = time.time()
    positions = [
        (i, (r, c))
        for i in set_I
        for c in range(0, l_bound - heights[i] + 1)
        for r in range(0, W - widths[i] + 1)
    ]
    print(f"POSITIONS TIME: {time.time() - s_time}")

    valid_positions = list(range(len(positions)))
    set_J = valid_positions

    tiles_strip = list(range(W * l_bound))
    set_P = tiles_strip

    def check_position(i, j):
        n_circuit, pos = positions[i]
        coord_x, coord_y = j % W, j // W
        return coord_x in range(
            pos[0], pos[0] + widths[n_circuit]
        ) and coord_y in range(pos[1], pos[1] + heights[n_circuit])

    s_time = time.time()
    correspondence_matrix = [[check_position(i, j) for j in set_P] for i in set_J]
    print(f"CORRISPONDENCE MATRIX TIME: {time.time() - s_time}")

    s_time = time.time()
    place = [
        [
            pulp.LpVariable(f"place_{i}_{j}", lowBound=0, upBound=1, cat=pulp.LpBinary)
            if positions[j][0] == i
            else None
            for j in set_J
        ]
        for i in set_I
    ]
    print(f"PLACE TIME: {time.time() - s_time}")

    s_time = time.time()
    for p in set_P:
        prob += (
            pulp.lpSum(
                [
                    correspondence_matrix[j][p] * place[i][j]
                    for i in set_I
                    for j in set_J
                    if positions[j][0] == i
                ]
            )
            <= 1
        )
    print(f"CONSTRAINTS 1 TIME: {time.time() - s_time}")

    s_time = time.time()
    for i in set_I:
        prob += pulp.lpSum([place[i][j] for j in set_J if positions[j][0] == i]) == 1
    print(f"CONSTRAITNS 2 TIME: {time.time() - s_time}")

    s_time = time.time()
    prob += (
        pulp.lpSum(
            [
                correspondence_matrix[j][p] * place[i][j]
                for i in set_I
                for j in set_J
                if positions[j][0] == i
                for p in set_P
            ]
        )
        <= W * l_bound
    )
    print(f"CONSTRAINTS 3 TIME: {time.time() - s_time}")

    return prob, positions, l_bound


def build_first_model(W: int, N: int, widths, heights) -> pulp.LpProblem:
    set_N = range(N)
    prob = pulp.LpProblem("vlsi", pulp.LpMinimize)
    # Lower and upper bounds for the height
    l_low = max(
        max(heights), math.ceil(sum([widths[i] * heights[i] for i in set_N]) / W)
    )
    l_up = int(sum(heights))

    # Height variable
    l = pulp.LpVariable("l", lowBound=l_low, upBound=l_up, cat=pulp.LpInteger)
    prob += l, "Height of the plate"

    # Coordinate variables
    coord_x = [
        pulp.LpVariable(
            f"coord_x_{i}", lowBound=0, upBound=int(W - widths[i]), cat=pulp.LpInteger
        )
        for i in set_N
    ]
    coord_y = [
        pulp.LpVariable(
            f"coord_y_{i}",
            lowBound=0,
            upBound=int(l_up - heights[i]),
            cat=pulp.LpInteger,
        )
        for i in set_N
    ]

    # Boundary constraints
    for i in set_N:
        # prob += coord_x[i] + widths[i] <= W, f"X-axis of {i}-th coordinate bound"
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

    max_circuit = np.argmax(np.asarray(widths) * np.asarray(heights))
    prob += coord_x[max_circuit] == 0, "Max circuit in x-0"
    prob += coord_y[max_circuit] == 0, "Max circuit in y-0"

    # Non-Overlap constraints, at least one needs to be satisfied
    for i in set_N:
        for j in set_N:
            if i < j:
                if widths[i] + widths[j] > W:
                    prob += delta[i][j][0] == 1
                    prob += delta[j][i][0] == 1
                # TODO test on these constraints
                if max_circuit == i:
                    prob += delta[j][i][1] == 1
                elif max_circuit == j:
                    prob += delta[i][j][1] == 1

                prob += coord_x[i] + widths[i] <= coord_x[j] + (delta[i][j][0]) * W
                prob += coord_x[j] + widths[j] <= coord_x[i] + (delta[j][i][0]) * W
                prob += coord_y[i] + heights[i] <= coord_y[j] + (delta[i][j][1]) * l_up
                prob += coord_y[j] + heights[j] <= coord_y[i] + (delta[j][i][1]) * l_up
                prob += (
                    delta[i][j][0] + delta[j][i][0] + delta[i][j][1] + delta[j][i][1]
                    <= 3
                )

                # TODO old constraints
                """ if widths[i] + widths[j] > W:
                    prob += delta[i][j][0] == 0
                    prob += delta[j][i][0] == 0

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
                ) """

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
    c_wh_up = min(widths + heights)
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
