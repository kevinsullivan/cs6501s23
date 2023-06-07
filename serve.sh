# OBSOLETE

#!/usr/bin/env bash

# set -e
# if [ "$#" -ne 2 ]; then
#     echo "Usage example: $0 cs6501s23"
#     exit 1
# fi

# Serve
pushd build/html
python3.8 -m http.server
popd

