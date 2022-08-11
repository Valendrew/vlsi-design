import matplotlib.pyplot as plt
import numpy as np


def plot(width, height, n, circuits, coords, path):
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

    fig = plt.figure(figsize=(width, width))
    plt.grid(visible=True)
    plt.xticks(np.arange(0, width+1, step=1))
    plt.yticks(np.arange(0, height+1, step=1))
    plt.imshow(image, origin="lower", extent=[0, width, 0, height])
    plt.savefig(path, bbox_inches="tight")
    plt.close(fig)
