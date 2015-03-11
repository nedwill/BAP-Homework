//red step, first test case
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

bool g(int x);

bool f(int x)
{
    if (x < 0)
        return false;
    if (x == 0)
        return true;
    else if (x == 1)
        return false;
    else
        return g(x-2);
}

bool g(int x)
{
    if (x < 0)
        return false;
    if (x == 0)
        return false;
    else if (x == 1)
        return true;
    else
        return f(x-2);
}

//this could tail call optimize and make things interesting
//might need -O0 to prevent that from happening
int fact(int x)
{
    if (x <= 0)
        return 1;
    else
        return x*fact(x-1);
}

void badcpy(int argc, char* argv[])
{
    char buf[16];
    if (argc != 2)
    {
        printf("Wrong number of args!\n");
        return;
    }
    strcpy(buf, argv[1]);
}

int main(int argc, char* argv[])
{
    badcpy(argc, argv);
    return 0;
}

