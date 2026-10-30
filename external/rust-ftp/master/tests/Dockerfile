FROM ubuntu:20.04

RUN apt-get update -qq &&\
    apt-get install -yqq vsftpd

ADD vsftpd.conf /etc/vsftpd.conf

RUN useradd -s /bin/bash -d /home/ftp -m -c "Doe ftp user" -g ftp Doe &&\
    echo "Doe:mumble"| chpasswd &&\
    echo "/etc/init.d/vsftpd start" | tee -a /etc/bash.bashrc

CMD ["/bin/bash"]
