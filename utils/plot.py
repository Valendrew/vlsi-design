import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.collections import PatchCollection

import numpy as np

from utils.types import SOLUTION_ADMISSABLE, Solution


def plot(width, height, n, circuits, coords, path, cmap_name="Set3"):
    image = np.zeros((width, height))
    # create image
    for i in range(0, n):
        block_w = int(circuits[i][0])
        block_h = int(circuits[i][1])
        pos_x = int(coords["x"][i])
        pos_y = int(coords["y"][i])

        image[pos_y : pos_y + block_h, pos_x : pos_x + block_w,] = (
            i + 1
        )

    cmap = plt.cm.get_cmap(cmap_name, n)
    fig = plt.figure(figsize=(width, width))
    plt.grid(visible=True)
    plt.xticks(np.arange(0, width + 1, step=1))
    plt.yticks(np.arange(0, height + 1, step=1))
    plt.imshow(image, origin="lower", extent=[0, width, 0, height], cmap=cmap)
    plt.savefig(path, bbox_inches="tight")
    plt.close(fig)


def plot_cmap(
    width, height, n, circuits, coords, path, rotation=None, cmap_name="Set3"
):
    fig = plt.figure(figsize=(width, width))
    ax = fig.add_subplot(111, aspect="equal")

    cmap = plt.cm.get_cmap(cmap_name, n)
    patches = []

    rotation = (
        [0 for _ in range(n)]
        if (rotation is None) or (len(rotation) == 0)
        else rotation
    )
    for i in range(0, n):
        circ_width = int(circuits[i][0]) if rotation[i] == 0 else int(circuits[i][1])
        circ_height = int(circuits[i][1]) if rotation[i] == 0 else int(circuits[i][0])
        coord_x = int(coords["x"][i])
        coord_y = int(coords["y"][i])
        patches.append(
            Rectangle(
                (coord_x, coord_y),
                circ_width,
                circ_height,
                ec="k",
                linewidth=1,
                facecolor=cmap(i),
            )
        )
    ax.add_collection(PatchCollection(patches, match_original=True))

    plt.grid(visible=True)
    plt.xticks(np.arange(0, width + 1, step=1))
    plt.yticks(np.arange(0, height + 1, step=1))
    plt.savefig(path, bbox_inches="tight")
    plt.close(fig)


def plot_solution(sol: Solution, plot_file: str):
    if SOLUTION_ADMISSABLE(sol.status):
        plot_cmap(
            sol.width,
            sol.height,
            sol.n_circuits,
            sol.circuits,
            sol.coords,
            plot_file,
            sol.rotation,
            "turbo_r",
        )
