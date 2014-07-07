#include <stdio.h>
#include <stdlib.h>

unsigned int htoi (const char *ptr)
{
unsigned int value = 0;
char ch = *ptr;

/*--------------------------------------------------------------------------*/

    while (ch == ' ' || ch == '\t')
        ch = *(++ptr);

    for (;;) {

        if (ch >= '0' && ch <= '9')
            value = (value << 4) + (ch - '0');
        else if (ch >= 'A' && ch <= 'F')
            value = (value << 4) + (ch - 'A' + 10);
        else if (ch >= 'a' && ch <= 'f')
            value = (value << 4) + (ch - 'a' + 10);
        else if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == 0)
            return value;
        else return -1;
        ch = *(++ptr);
    }
}

int main (int argc, char* argv[]) {
  FILE * pFile;
  FILE * pOut;
  long lSize;
  char * buffer;
  char * p;
  int count;
  int i;
  size_t result;

  if (argc < 3)
    {
      puts("usage: hexbin <input-file> <output-file>\n");
      exit(1);
    }
  pFile = fopen ( argv[1] , "rb" );
  if (pFile==NULL) {fputs ("File error",stderr); exit (1);}

  // obtain file size:
  fseek (pFile , 0 , SEEK_END);
  lSize = ftell (pFile);
  rewind (pFile);

  // allocate memory to contain the whole file:
  buffer = (char*) malloc (sizeof(char)*lSize);
  if (buffer == NULL) {fputs ("Memory error",stderr); exit (2);}

  // copy the file into the buffer:
  result = fread (buffer,1,lSize,pFile);

  if (result != lSize) {fputs ("Reading error",stderr); exit (3);}

  /* the whole file is now loaded in the memory buffer. */

  // terminate
  fclose (pFile);

  pOut = fopen (argv[2], "wb");
  if (pOut==NULL) {fputs ("File error",stderr); exit (1);}

  p = buffer;
  // Find equals sign
  while (*p && *p != '"') { p++; }
  if (*p == 0) { exit(1); }

  // Find opening quotation marks
  while (*p && *p != '"') { p++; }
  if (*p == 0) { exit(1); }

  if (*p) {
    p++;
    while (*p && *p != '"') {
      // Decode hex
      i = htoi(p);
      if (i < 0) { fclose(pOut); exit (1); }
      fputc(i, pOut);
      p += 2;
      while (*p == ' ' || *p == '\n' || *p == '\r') p++;
    }
  }
  fclose(pOut);
  free (buffer);


  return 0;
}
