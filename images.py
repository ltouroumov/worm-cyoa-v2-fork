import json
from PIL import Image
import base64
import io
import humanize

def image_info(image_data):
    try:
        header, contents = str.split(image_data, ';')
        encoding, data_str = str.split(contents, ',')

        if encoding == 'base64':
            try:
                data_bytes = base64.b64decode(data_str)
            except Exception:
                return 0, f"Failed to decode data"
        else:
            return 0, f"Unsupported encoding {encoding}"

        image_size = len(data_bytes)
        image = Image.open(io.BytesIO(data_bytes))
        return image_size, f"{header}({humanize.naturalsize(image_size)}, {image.size})"
    except Exception as e:

        return 0, f"Error while reading '{image_data[:64]}': {type(e)}"

MAX_IMAGE_SIZE = 1_000_000

if __name__ == '__main__':
    with open('project-v12.json', mode='r') as fd:
        project = json.load(fd)

    big_images = []
    total_image_bytes = 0
    for row in project['rows']:
        row_image_bytes = 0
        if (img := row['image']) != '':
            img_size, desc = image_info(img)
            if img_size > MAX_IMAGE_SIZE:
                big_images.append(f"{row['title']} : {desc}")
            row_image_bytes += img_size
            print(f"Row '{row['title']}': {desc}")
        else:
            print(f"Row '{row['title']}'")

        for obj in row['objects']:
            if (img := obj['image']) != '':
                img_size, desc = image_info(img)
                if img_size > MAX_IMAGE_SIZE:
                    big_images.append(f"{row['title']}/{obj['title']} : {desc}")
                row_image_bytes += img_size
                print(f"  Obj: {obj['title']}: {desc}")
        
        if row_image_bytes > 0:
            print(f"Row '{row['title']}' total {humanize.naturalsize(row_image_bytes)}")
            total_image_bytes += row_image_bytes

    print(f"File total {humanize.naturalsize(total_image_bytes)}")
    print(f"Images larger than {humanize.naturalsize(MAX_IMAGE_SIZE)}")
    for name in big_images:
        print(f"- {name}")
