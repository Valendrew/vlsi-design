def extract_input_from_txt(data_path, file_instance):
    data_file = data_path.format(file=file_instance)
    with open(data_file, 'r') as fin:
        text = [line.rstrip() for line in fin.readlines()]
            
    W, N = int(text.pop(0)), int(text.pop(0))
    widths, heights = [], []
    for val in text:
        w, h = val.split()
        widths.append(int(w))
        heights.append(int(h))
    return W, N, widths, heights
