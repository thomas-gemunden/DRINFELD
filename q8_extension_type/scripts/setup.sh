#!/bin/sh
# Set up the working directory for the Q_8 extension-type investigation.
# After running this, you can invoke any of the *.g scripts here directly
# from this directory:
#
#     gap -q -b -c 'Read("verify_q8.g");'
#
# The scripts use Gruen's LoadModularData(n, m, k) helper (defined in
# ../../src/modular_data.g) which reads the data files from a directory
# called "Modular_Data" (with capital M, D) in the current working
# directory.  We create that as a symlink to the (sibling-of-DRINFELD)
# modular_data data tree.
#
# Symlink target: ../../../modular_data  resolves to
#     DRINFELD/q8_extension_type/scripts/../../../modular_data
#   = group_cohomology/modular_data

set -e

cd "$(dirname "$0")"

if [ ! -e "Modular_Data" ]; then
  ln -s ../../../modular_data Modular_Data
  echo "created symlink: $(pwd)/Modular_Data -> ../../../modular_data"
else
  echo "Modular_Data already exists, leaving it alone"
fi

# Confirm the symlink resolves to actual data.
if [ ! -d "Modular_Data/8/4" ]; then
  echo "WARNING: Modular_Data/8/4 not found." >&2
  echo "  Make sure ../../../modular_data exists and contains the" >&2
  echo "  precomputed Q_8 modular data (cocycle files 1.txt..8.txt)." >&2
  exit 1
fi

echo "OK: $(ls Modular_Data/8/4 | wc -l | tr -d ' ') files visible under Modular_Data/8/4/"
