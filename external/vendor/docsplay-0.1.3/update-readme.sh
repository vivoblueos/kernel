#! /usr/bin/env bash

cargo readme -o ./README.md
git add ./README.md
git commit -m "Update readme" || true
