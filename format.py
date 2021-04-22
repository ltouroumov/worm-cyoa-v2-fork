import sys, json
from shutil import copyfile

if __name__ == "__main__":
    project_file = sys.argv[1]
    print(f"Loading Project from {project_file}")
    with open(project_file, mode='r') as fd:
        project = json.load(fd)

    copyfile(project_file, project_file + ".bak")
    with open(project_file, mode='w+') as fd:
        json.dump(project, fd, indent=2, sort_keys=True)
