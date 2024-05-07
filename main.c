#include <stdio.h>

extern int main_t();

int main(){

    int ans = 0;
    ans = main_t();

    printf("%d", ans);

    return 0;
}