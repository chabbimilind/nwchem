#include<stdio.h>
int Foo(){
	void * ra = __builtin_return_address(15);
	void * frame = __builtin_frame_address(0);
	printf("%p %p", ra, frame);
	return 0;
}

int main(){
	Foo();
	return 0;
}

