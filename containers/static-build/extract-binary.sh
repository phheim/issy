#!/bin/sh 

podman unshare /bin/sh -c 'mnt=$(podman image mount issy-static-builder) && cp "${mnt}/home/user/build/issy" issy-static'

