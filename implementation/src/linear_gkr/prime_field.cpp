#include "linear_gkr/prime_field.h"
#include <cmath>
#include <climits>
#include <ctime>
#include <iostream>
using namespace std;
typedef unsigned long long uint64;

#define MASK 4294967295 //2^32-1
#define PRIME 2305843009213693951 //2^61-1
namespace prime_field
{
	uint64 myMod(uint64 x)
	{
  		return (x >> 61) + (x & PRIME);
	} 
	u64b::u64b()
	{
		value_64 = 0;
	}
	u64b::u64b(const int &b)
	{
		value_64 = b;
	}
	u64b::u64b(const uint64 &b)
	{
		value_64 = b;
	}
	u64b u64b::operator + (const u64b &b) const
	{
		u64b ret;
		ret.value_64 = myMod(b.value_64) + myMod(value_64);
		// ret.value_64 = (b.value_64) + (value_64);

		return ret;
	}
	u64b u64b::operator - (const u64b &b) const
	{
		u64b ret;
		ret.value_64 =value_64 + PRIME - b.value_64;
		return ret;
	}
	u64b u64b::operator * (const u64b &b) const
	{
		u64b ret;
		
		uint64 x = value_64;
		uint64 y = b.value_64;
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
		uint64 result = myMod(piece1 + piece2 + piece3)%mod;

		ret.value_64 = result;
		return ret;
	}
	u64b u64b::operator % (const uint64 &b) const
	{
		u64b ret;
		ret.value_64 = myMod(value_64);
		return ret;
	}
	bool u64b::operator < (const u64b &b) const
	{
		if(value_64<b.value_64)
		{
			return true;
		}
		else
			return false;
	}
	bool u64b::operator > (const u64b &b) const
	{
		if(value_64 > b.value_64)
			return true;
		if(value_64 <= b.value_64)
			return false;
		
	}
	bool u64b::operator >= (const u64b &b) const
	{
		if(value_64 >= b.value_64)
			return true;
		if(value_64 < b.value_64)
			return false;
		
	}

	bool u64b::operator != (const u64b &b) const
	{
		if(myMod(value_64)%PRIME != myMod(b.value_64)%PRIME)
			return true;
		else
			return false;
		
	}
	uint64 mod;
	bool initialized = false;
	void init(std::string s, int base)
	{
		assert(base == 10);
		initialized = true;
		mod = stoll(s);
	}

	void init_random()
	{
	}
	mpz_class field_element::to_gmp_class()
	{
		mpz_class ret(std::to_string(myMod(value.value_64)%mod));
		return ret;
	}
	field_element::field_element()
	{
		value.value_64 = (uint64)(0);
	}
	field_element::field_element(const int x)
	{
		value.value_64 = (uint64)(x);
	}
	field_element::field_element(const unsigned long long x)
	{
		value.value_64 = (uint64)(myMod(x));
	}
	field_element::field_element(std::string str)
	{
		value.value_64 = strtoull(str.c_str(), nullptr, 10);
	}
	field_element field_element::operator + (const field_element &b) const
	{

		field_element ret;
		ret.value = b.value + value;
		return ret;
	}
	field_element field_element::operator - (const field_element &b) const
	{

		field_element ret;
		ret.value = value - b.value;
		return ret;
	}
	field_element field_element::operator * (const field_element &b) const
	{
		field_element ret;
		ret.value = value * b.value;
		return ret;
	}
	bool field_element::operator == (const field_element &b) const
	{
		return !(*this != b);
	}
	bool field_element::operator >= (const field_element &b) const
	{
		if(value >= b.value){
			return true;
		}return false;
	}
	bool field_element::operator > (const field_element &b) const
	{
		if(value>b.value){
			return true;
		}	
		return false;
	}
	bool field_element::operator <= (const field_element &b) const
	{
		if(value >b.value){
			return false;
		}return true;
	}
	bool field_element::operator < (const field_element &b) const
	{
		if(value <b.value){
			return true;
		}return false;
	}
	bool field_element::operator != (const field_element &b) const
	{
		return (value) != (b.value);
	}
	field_element random()
	{
		field_element ret;
		ret.value = rand()%100;
		ret.value = 32; //change this later
		return ret;
	}



}
