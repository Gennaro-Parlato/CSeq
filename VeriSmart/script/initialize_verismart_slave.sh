echo "65536\n" | sudo -S mount -t nfs master:/home/aldo/CSeq-master /home/aldo/CSeq-master

#to avoid to manually mount the shared master directory every time you do a system reboot:
echo "master:/home/aldo/CSeq-master /home/aldo/CSeq-master nfs" | sudo tee -a /etc/fstab

sudo pip3 install -r /home/aldo/CSeq-master/VeriSmart/requirements.txt