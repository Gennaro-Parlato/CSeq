
echo "$2 $1" | sudo tee -a /etc/hosts
echo "$1 slots=$3" | sudo tee -a /home/aldo/CSeq-master/VeriSmart/nodes
ssh-copy-id aldo@$1