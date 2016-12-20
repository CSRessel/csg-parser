CC=g++
CFLAGS=-pedantic -Wall -Wshadow -Wextra -Werror -lreadline -std=gnu++11
OUTPUT=csgp.out

all: main.cpp
	$(CC) $(CFLAGS) -o $(OUTPUT) main.cpp

