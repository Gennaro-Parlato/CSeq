
# install all required libraries to use verismart
sudo apt update
sudo apt install gcc-multilib -qq --yes
sudo apt install g++-multilib -qq --yes
sudo apt install libc6-dev-i386 -qq --yes
sudo apt install libopenmpi-dev -qq --yes
sudo apt install unzip -qq --yes
sudo apt install openmpi-bin -qq --yes
sudo apt install python3 -qq --yes
sudo apt install python3-pip -qq --yes
sudo apt-get install nfs-kernel-server -qq --yes
sudo apt-get install nfs-common -qq --yes
sudo apt install sshpass -qq --yes
sudo apt install cbmc -qq --yes

# add environment variables to use openmpi from next reboot
echo "export PATH=/usr/lib64/openmpi/bin:$PATH" >> /home/ubuntu/.bashrc
echo "export LD_LIBRARY_PATH=/usr/lib64/openmpi/lib" >> /home/ubuntu/.bashrc

# add environment variables to use openmpi
export PATH=/usr/lib64/openmpi/bin:$PATH
export LD_LIBRARY_PATH=/usr/lib64/openmpi/lib

# declare an hostname for each EC2 instances associated to its IP address on hosts file
echo "10.0.0.58 master" | sudo tee -a /etc/hosts
echo "10.0.0.119 slave1" | sudo tee -a /etc/hosts
echo "10.0.0.72 slave2" | sudo tee -a /etc/hosts
echo "10.0.0.120 slave3" | sudo tee -a /etc/hosts
echo "10.0.0.36 slave4" | sudo tee -a /etc/hosts
echo "10.0.0.64 slave5" | sudo tee -a /etc/hosts
echo "10.0.0.182 slave6" | sudo tee -a /etc/hosts

# CREATE USER IS MISSING
sudo useradd -m -p $(echo "65536" | openssl passwd -1 -stdin) aldo
#echo -e "65536\n65536\n\n\n\n\ny" | sudo adduser aldo

# machines are going to talk over the network via ssh through a SSH server which is already installed in EC2 instances
# to simplify configuration an authentication we will enable password authentication which will replace token (keypair) authentication
sed '/PasswordAuthentication/d' /etc/ssh/sshd_config > sshd_config
> /etc/ssh/sshd_config
sudo cp -f ./sshd_config /etc/ssh/sshd_config
echo "PasswordAuthentication yes" | sudo tee -a /etc/ssh/sshd_config

# restart the ssh server service which will have enabled the password authentication:
sudo service ssh restart

sudo mkdir -m 777 /home/aldo/.ssh

#sudo touch /home/aldo/.ssh/id_rsa

#sudo touch /home/aldo/.ssh/id_rsa.pub

sudo ssh-keygen -t rsa -f /home/aldo/.ssh/id_rsa -q -P '65536'

sudo ssh-keyscan master | sudo tee -a /home/aldo/.ssh/known_hosts

#sudo sshpass -p '65536' ssh -o StrictHostKeyChecking=no aldo@slave6 "ssh-copy-id -f -i /home/aldo/.ssh/id_rsa aldo@master"

sudo sshpass -p '65536' ssh-copy-id -f -i /home/aldo/.ssh/id_rsa aldo@master

sudo mkdir /home/aldo/CSeq

echo "65536\n" | sudo -S mount -t nfs master:/home/aldo/CSeq /home/aldo/CSeq

#to avoid to manually mount the shared master directory every time you do a system reboot:
echo "master:/home/aldo/CSeq /home/aldo/CSeq nfs" | sudo tee -a /etc/fstab

sudo pip3 install -r /home/aldo/CSeq/VeriSmart/requirements.txt
