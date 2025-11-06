#!/bin/bash
DEST="$HOME/just_install"
# create ~/just_install
mkdir -p "$DEST"

# download and extract just to ~/just_install/just
curl --proto '=https' --tlsv1.2 -sSf https://just.systems/install.sh | bash -s -- --to "$DEST"

# add `~/just_install` to the paths that your shell searches for executables
# this line should be added to your shells initialization file,
# e.g. `~/.bashrc` or `~/.zshrc`
export PATH="$PATH:$DEST"

# just should now be executable
just --help
