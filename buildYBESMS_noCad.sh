#!/bin/bash

cd satsuma
cmake .
make satsuma
cd ../ybe-sms
rm -r ./build/
cmake . -B./build
cd ./build/
make