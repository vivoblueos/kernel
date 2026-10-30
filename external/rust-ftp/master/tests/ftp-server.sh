#!/bin/sh

# run the ftp server instance in detached mode (in the background)
# but also with TTY and interactive mode, so we can attach to it if we want to
docker run -dti --privileged -p 21:21 -p 65000-65010:65000-65010 ftp-server
