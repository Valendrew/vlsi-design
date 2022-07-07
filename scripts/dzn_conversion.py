import os

INPUT_FOLDER = "./vlsi-instances/txt-instances"
OUTPUT_FOLDER = "./vlsi-instances/dzn-instances"


def create_dzn_file(filename: str):
    """Reads a txt instance and returns a dzn instance, formatted as:\n
    W = plate_width;\n
    N = circuits_number;\n
    CIRCUITS = [| x_1, y_1 |\n
    \t\t\t ....., .....     |\n
    \t\t     x_N, y_N |];"""

    with open(os.path.join(INPUT_FOLDER, filename), "r") as f:
        lines = [line.rstrip() for line in f]

    if len(lines) > 0:
        plate_width = int(lines[0])
        circuits_number = int(lines[1])

        dzn_circuits = "[|"
        if len(lines) == circuits_number + 2:

            for i in range(circuits_number):
                circuit = lines[i + 2].split(" ")
                dzn_circuits += f" {circuit[0]}, {circuit[1]} |\n\t\t\t\t\t\t "

        dzn_circuits = dzn_circuits.rstrip()
        dzn_circuits += "]"

        dzn_output = f"""W = {plate_width};\nN = {circuits_number};\nCIRCUITS = {dzn_circuits};"""

        output_file = filename.split(".txt")[0] + ".dzn"

        with open(os.path.join(OUTPUT_FOLDER, output_file), "w") as f:
            f.write(dzn_output)


files_list = [
    f for f in os.listdir("./vlsi-instances/txt-instances") if f.endswith(".txt")
]

for f in files_list:
    create_dzn_file(f)
    print(f"{f} converted to data file")
