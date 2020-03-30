#!/bin/bash

if [  $# -ne 1 ]; then
	echo "Usage: ./build <map_pow2>"
	exit 1
fi

make clean
make MAP_SIZE_POW2=$1
cd llvm_mode
make MAP_SIZE_POW2=$1

