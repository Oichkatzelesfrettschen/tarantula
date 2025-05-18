#!/bin/sh
set -e
TMPDIR=/tmp/pathtrans_test
rm -rf $TMPDIR
mkdir -p $TMPDIR/orig $TMPDIR/new

echo "data" > $TMPDIR/new/file.txt
DB=$TMPDIR/db.txt
export PATHTRANS_DB=$DB
../tools/pathtrans_db -a $TMPDIR/orig $TMPDIR/new
export LD_PRELOAD=../libpathtrans.so
./test_translation
RET=$?
rm -rf $TMPDIR
exit $RET
