#include<builtins.h>
#include<stdint.h>
#include<stdio.h>

int main(){
	uint64_t a[1000];
	uint64_t b[1000];
	uint64_t oldVal = __ldarx((volatile long *)a);
	uint64_t oldVal2 = __ldarx((volatile long *)b);
	if(__stdcx((volatile long *)a, 1)) {
		printf("\n Successfully stored via __ldarx to a[]");
	} else {

		printf("\n Failed to store via __ldarx to a[]");
	}
	return 0;
}
