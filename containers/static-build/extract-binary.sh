#!/bin/sh 

podman run --rm issy-static-builder /bin/sh -c 'cat /home/user/build/issy' > issy-static
chmod +x issy-static
