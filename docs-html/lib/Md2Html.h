#ifndef MD2HTML_H
#define MD2HTML_H

// forward definitions of required Carp functionality
typedef char *Carp_String;                   // should we ever chamge typedef String, the linker will complain!
Carp_String String_from_MINUS_cstr(char *s); // implementation (!) is in carp_string.h


// this function does the actual work
Carp_String Md2Html_convert(Carp_String *in);


#endif
