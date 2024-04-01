#include "linear_gkr/prime_field_small.h"
#include <cmath>
#include <climits>
#include <ctime>
#include <iostream>
using namespace std;
typedef unsigned long long uint64;

#define MASK 4294967295 //2^32-1
#define PRIME 2305843009213693951 //2^61-1
namespace prime_field_small
{
	
	uint64 mod;
	bool initialized = false;
	void init(std::string s, int base)
	{
		cout<<"here"<<endl;
		assert(base == 10);
		initialized = true;
		mod = stoll(s);


	}
	field_element::field_element()
	{
		value = (unsigned long long)0;
	}
	field_element::field_element(const int x)
	{
		value = (unsigned long long)x;
	}
	field_element::field_element(const unsigned long long x)
	{
		value = (unsigned long long)x;
	}
	uint64 myMod(uint64 x)
	{
  		return (x >> 61) + (x & PRIME);
	}  
	field_element field_element::operator + (const field_element &b) const
	{
		field_element ret;
		ret.value = (b.value + value);
		return ret;
	}
	field_element field_element::operator - (const field_element &b) const
	{
		field_element ret;
		if(value >= b.value)
			ret.value = value - b.value;
		else
			ret.value = value + PRIME - b.value;
		return ret;
	}
	field_element field_element::operator * (const field_element &b) const
	{
		field_element ret;
		
		uint64 x = value;
		uint64 y = b.value;

		uint64 hi_x = x >> 32;
		uint64 hi_y = y >> 32;
		uint64 low_x = x & MASK;
		uint64 low_y = y & MASK;
		//since myMod might return something slightly large than 2^61-1,  
		//we need to multiply by 8 in two pieces to avoid overflow.
		uint64 piece1 = myMod((hi_x * hi_y)<< 3);
		uint64 z = (hi_x * low_y + hi_y * low_x);
		uint64 hi_z = z >> 32;
		uint64 low_z = z & MASK;

		//Note 2^64 mod (2^61-1) is 8
		uint64 piece2 = myMod((hi_z<<3) + myMod((low_z << 32)));
		uint64 piece3 = myMod(low_x * low_y);
		uint64 result = myMod(piece1 + piece2 + piece3);

		ret.value = result;
		return ret;
	}
	bool field_element::operator < (const field_element &b) const
	{
		return !(*this >= b);
	}
	bool field_element::operator > (const field_element &b) const
	{
		return !(*this <= b);
	}
	bool field_element::operator == (const field_element &b) const
	{
		return !(*this != b);
	}
	bool field_element::operator >= (const field_element &b) const
	{
		return !(*this < b);
	}
	bool field_element::operator <= (const field_element &b) const
	{
		return !(*this > b);
	}
	bool field_element::operator != (const field_element &b) const
	{
		return value != b.value;
	}
	mpz_class field_element::to_gmp_class()
	{
		mpz_class ret(std::to_string(value));
		return ret;
	}


}
