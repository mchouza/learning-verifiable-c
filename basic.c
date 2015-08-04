unsigned int sum(unsigned int a, unsigned int b)
{
	return a + b;
}

unsigned int mul(unsigned int a, unsigned int b)
{
	return a * b;
}

unsigned mul2(unsigned a, int b)
{
	unsigned c = 0;
	for (int i = 0; i < b; i++)
		c += a;
	return c;
}

unsigned mul3(unsigned a, unsigned b)
{
	unsigned c = 0;
	unsigned i = 0;
	while (i < b)
	{
		c += a;
		i++;
	}
	return c;
}

unsigned mul4(unsigned a, unsigned b)
{
	unsigned c = 0;
	for (unsigned i = 0; i < b; i++)
		c += a;
	return c;
}