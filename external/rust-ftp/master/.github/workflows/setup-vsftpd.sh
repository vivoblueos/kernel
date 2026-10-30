#!/bin/bash

sudo apt-get update -qq &&
  sudo apt-get install -yqq vsftpd &&
  sudo useradd -s /bin/bash -d /home/ftp -m -c "Doe ftp user" -g ftp Doe &&
  echo "Doe:mumble" | sudo chpasswd &&
  cat $GITHUB_WORKSPACE/tests/vsftpd.conf | sudo tee /etc/vsftpd.conf &&
  cat /etc/vsftpd.conf &&
  sudo service vsftpd restart &&
  sudo service vsftpd status
