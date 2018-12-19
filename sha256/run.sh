# (cd ..;  ./mybuild.sh)
rsync -avzP --delete --exclude=target --exclude=Cargo.toml ~/ZoKrates_mac/ ~/ZoKrates
ln -s ../target/debug/zokrates .
./zokrates compile -i single_test.code 2>&1 | tee debugcomp 
./zokrates compute-witness 2>&1 | tee debugwit 