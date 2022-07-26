
# install all required libraries to use the ditributed version of verismart:
# - compile c, c++ languages
# - compile c, c++ languages with openmpi protocol
# - interpret python code and install python packages
# - use a distributed file system among different AWS EC2 instances
# - automate SSH commands in bash scripts
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

# add environment variables to:
# - compile with openmpi
# - use cbmc as binary of operative system
# on next reboot
echo "export PATH=/usr/lib64/openmpi/bin:$PATH" >> /home/ubuntu/.bashrc
echo "export LD_LIBRARY_PATH=/usr/lib64/openmpi/lib" >> /home/ubuntu/.bashrc

# add environment variables to:
# - compile with openmpi
# - use cbmc as binary of operative system
export PATH=/usr/lib64/openmpi/bin:$PATH
export LD_LIBRARY_PATH=/usr/lib64/openmpi/lib

# declare an hostname for each EC2 instances associated to its IP address on hosts file
# every instance should belong to the same VPC
# such that they can communicate through their private IP
echo "10.0.0.58 master" | sudo tee -a /etc/hosts
echo "10.0.0.119 slave1" | sudo tee -a /etc/hosts
echo "10.0.0.72 slave2" | sudo tee -a /etc/hosts
echo "10.0.0.120 slave3" | sudo tee -a /etc/hosts
echo "10.0.0.36 slave4" | sudo tee -a /etc/hosts

# create a user to enable the communication through the password among instances
# this user folder will contain verismart
sudo useradd -m -p $(echo "65536" | openssl passwd -1 -stdin) aldo

# machines are going to talk over the network via SSH through a SSH server which is already installed in EC2 instances
# to simplify configuration an authentication we will enable password authentication which will replace token (keypair) authentication
sed '/PasswordAuthentication/d' /etc/ssh/sshd_config > sshd_config
> /etc/ssh/sshd_config
sudo cp -f ./sshd_config /etc/ssh/sshd_config
echo "PasswordAuthentication yes" | sudo tee -a /etc/ssh/sshd_config

# when we try to connect through ssh to another machine, ubuntu tries to check if the host is authentic
# this check must be removed otherwise instance can't be enabled automatically the passwordless communication among instances
# with passwordless communication instance can work together through MPI
echo "StrictHostKeyChecking no" | sudo tee -a /etc/ssh/ssh_config

# restart the ssh server service which will have:
# - enabled the password authentication
# - disabled the authenticity check for new instance
sudo service ssh restart
