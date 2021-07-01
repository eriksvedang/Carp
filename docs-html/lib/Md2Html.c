/*
 * this code is a slightly simplified version of ./md2html/md2html.c from:
 *
 * 
 * MD4C: Markdown parser for C 
 * (http://github.com/mity/md4c)
 *
 * Copyright (c) 2016-2020 Martin Mitas
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "md4c-html.h"

// includes for Carp definitions
#include "Md2Html.h"

/* Global options. */
static unsigned parser_flags = 0;
#ifndef MD4C_USE_ASCII
    static unsigned renderer_flags = MD_HTML_FLAG_DEBUG | MD_HTML_FLAG_SKIP_UTF8_BOM;
#else
    static unsigned renderer_flags = MD_HTML_FLAG_DEBUG;
#endif


/*********************************
 ***  Simple grow-able buffer  ***
 *********************************/

struct membuffer {
    char* data;
    size_t asize;
    size_t size;
};

static void
membuf_init(struct membuffer* buf, MD_SIZE new_asize)
{
    buf->size = 0;
    buf->asize = new_asize;
    buf->data = malloc(buf->asize);
    if(buf->data == NULL) {
        fprintf(stderr, "membuf_init: malloc() failed.\n");
        exit(1);
    }
}

static void
membuf_fini(struct membuffer* buf)
{
    if(buf->data)
        free(buf->data);
}

static void
membuf_grow(struct membuffer* buf, size_t new_asize)
{
    buf->data = realloc(buf->data, new_asize);
    if(buf->data == NULL) {
        fprintf(stderr, "membuf_grow: realloc() failed.\n");
        exit(1);
    }
    buf->asize = new_asize;
}

static void
membuf_append(struct membuffer* buf, const char* data, MD_SIZE size)
{
    if(buf->asize < buf->size + size)
        membuf_grow(buf, buf->size + buf->size / 2 + size);
    memcpy(buf->data + buf->size, data, size);
    buf->size += size;
}


/**********************
 ***  Main program  ***
 **********************/

static void
process_output(const MD_CHAR* text, MD_SIZE size, void* userdata)
{
    membuf_append((struct membuffer*) userdata, text, size);
}

Carp_String
Md2Html_convert(Carp_String *in)
{
    Carp_String result = NULL;

    struct membuffer buf_in = {0};
    struct membuffer buf_out = {0};

    buf_in.data = *in;
    buf_in.size = strlen(*in);      // length of *in, excluding the terminating null byte!
    buf_in.asize = buf_in.size+1;   // the buffer needs the additional null byte


    /* Input size is good estimation of output size. Add some more reserve to
     * deal with the HTML header/footer and tags. */
    membuf_init(&buf_out, buf_in.size + buf_in.size/8 + 64);

    /* Parse the document. This shall call our callbacks provided via the
     * md_renderer_t structure. */

    int ret = md_html(buf_in.data, buf_in.size, process_output, (void*) &buf_out,
                    parser_flags, renderer_flags);

    if(ret != 0) {
        // Parsing failed
        result = NULL;
    }
    else {
        /* Success if we have reached here. */
        result = String_from_MINUS_cstr( buf_out.data );
    }

    // do NOT call membuf_fini(&buf_in); here since the input buffer is managed in the calling Carp code!
    membuf_fini(&buf_out);

    return result;
}

