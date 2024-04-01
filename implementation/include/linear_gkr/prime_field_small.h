#pragma once

// #ifndef __prime_field_small
// #define __prime_field_small

#include <cassert>
#include <string>
#include <gmp.h>
#include <gmpxx.h>
#include <vector>
typedef unsigned long long uint64;

namespace prime_field_small
{
	void init(std::string, int);

	class field_element
	{
	private:
	public:
		uint64 value;

		field_element();
		field_element(const int);
		field_element(const unsigned long long);
		field_element operator + (const field_element &b) const;
		field_element operator * (const field_element &b) const;
		field_element operator / (const field_element &b) const;
		field_element operator - (const field_element &b) const;
		bool operator == (const field_element &b) const;
		bool operator >= (const field_element &b) const;
		bool operator <= (const field_element &b) const;
		bool operator > (const field_element &b) const;
		bool operator < (const field_element &b) const;
		field_element mul_non_mod(const field_element &b) const;
		char* to_string();
		int bitLen();
		bool operator != (const field_element &b) const;
		mpz_class to_gmp_class();
		std::vector<bool> bit_stream();
	};
}