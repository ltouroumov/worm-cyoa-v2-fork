#!/bin/bash

if [ "$#" -lt "2" ]; then
	echo "build.sh file.json v00"
	exit 1
fi

INPUT=$1
VERSION=$2
BUILD="viewer"
if [ "$#" == "3" ]; then
    BUILD=$3
fi

PROJECT="project-$VERSION.json"

cp "$INPUT" $PROJECT
python3 format.py $PROJECT
python3 build.py $PROJECT $BUILD
git status
