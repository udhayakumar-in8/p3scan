/*
 * P3Scan v2.3.2
 *
 * (C) 2003-2005 by Jack S. Lai <laitcg@cox.net>
 *
 * It's intent is to provide a follow on program to POP3-Virusscan-Proxy 0.4
 * by Folke Ashberg <folke@ashberg.de>.
 *
 * It is based upon his program but provides numerous changes to include
 * scanning pop3 mail for spam, hardening the program, addaption to todays
 * email environment, and many other changes.
 *
 * The initial release of p3scan includes patches made and submitted to the
 * original project but were never incorporated. Please see the README for
 * further information.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * This program is released under the GPL with the additional exemption that
 * compiling, linking, and/or using OpenSSL is allowed."
 * (http://www.openssl.org/support/faq.html#LEGAL2)
 *
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <malloc.h>
#include <stdarg.h>
#include <fcntl.h>
#include <sys/time.h>
#include <errno.h>

#include "getlinep3.h"

extern void * w_malloc(size_t bytes);
extern void w_free(void *f_address);

int secure_write(int fd, char * buf, int len){
   /* writes len bytes from buf to fd */
   /* repeats if fd can't send len at once */
   /* returns error or number of bytes written */
   int written=0;
   int i;
   if (len==0) return GETLINE_OK; /* that's ok */
   if (len<1)  return GETLINE_ERR; /* grmpf, that's not */
   while ((i=write(fd, &buf[written], len-written))<len){
      /* Socket went away */
      if (i==-1 && errno==EPIPE) return GETLINE_PIPE;
      /* Other errors */
      if (i<1) return GETLINE_ERR;
      written+=i;
      len-=i;
   }
   return written;
}

int select_fd_read(int fd){
   /* calls select (on read) for a given fd) */
   fd_set fds;
   struct timeval timeout;
   timeout.tv_sec = 0;
   timeout.tv_usec = 0;
   FD_ZERO(&fds);
   FD_SET(fd, &fds);
   return select(fd + 1, &fds, NULL, NULL, &timeout);
}

int getlinep3(int fd, struct linebuf * l){
   int len=0, last_r, maxread;
   char *p;
   /* is there one more line in buf? */
   if (l->lineend == l->bufend){
      /* no --> read some chars */
      maxread=l->max -1;
      if (maxread<1) return GETLINE_TOO_LONG;
      if (select_fd_read(fd)<1) return GETLINE_NEED_READ;
      len=read(fd, l->buf, maxread );
      if (len<1) return GETLINE_EOF;
      l->len=len;
      l->line=l->buf;
      l->bufend=&(l->buf[len-1]);
   } else {
      /* move next line (from which we have already some data) to beginning of buf */
      if (l->lineend && l->bufend){
         len=l->bufend - l->lineend;
         memmove(l->buf, l->lineend +1, len );
         l->line=l->buf;
         l->bufend=l->buf + len -1 ;
         l->len=len;
      } else {
         /* there is a not yet finished line in buf */
         maxread=l->max - l->len -1;
         if (maxread<1){ /* no more space left in buf */
            if (l->len == l->max){
               l->linelen=l->max-1;
               //l->buf[l->max-1]='\0';
            } else {
               l->linelen=l->len-1;
               //l->buf[len]='\0';
            }
            l->line=l->buf;
            /* set to zero, then next call will work */
            l->len=0;
            l->lineend=NULL;
            l->bufend=NULL;
            return GETLINE_TOO_LONG;
         }
         if (select_fd_read(fd)<1) return GETLINE_NEED_READ;
         len=read(fd, &(l->buf[l->len]), maxread );
         if (len<1){   /* EOF */
            /* TODO: what's up if last line has no [\r]\n ? */
            l->moredata=0;
            l->linelen=GETLINE_LINE_NULL;
            l->line=l->buf;
            l->buf[0]='\0';
            return GETLINE_EOF;
         }
         l->len+=len;
         l->line=l->buf;
         l->bufend=&(l->buf[l->len-1]);
      }
   }
   last_r=0;
   p=l->buf;
   while (p <= l->bufend ){
      switch (*p) {
         case '\r':
            last_r=1;
            break;
         case '\n':
            l->lineend=p;
            *p='\0';
            if (last_r) *(p-1)='\0';
            l->linelen=strlen(l->line);
            l->moredata=(l->lineend != l->bufend);
            return GETLINE_OK; /* voila, there is a line */
            break;
         default:
            last_r=0;
      }
      p++;
   }
   l->lineend=NULL;
   l->linelen=GETLINE_LINE_INCOMPLETE;
   l->moredata=0;
   return GETLINE_NOLINE; /* could not complete a whole line */
}

int writeline(int fd, int leading, char * c){
   char * out;
   int len, res;
   if (!c) return GETLINE_ERR;
   //--out=malloc(strlen(c)+3);
   out=w_malloc(strlen(c)+3);
   switch (leading){
      case WRITELINE_LEADING_NONE:
         len=sprintf(out, "%s", c);
         break;
      case WRITELINE_LEADING_N:
         len=sprintf(out, "%s\n", c);
         break;
      case WRITELINE_LEADING_RN:
      default:
         len=sprintf(out, "%s\r\n", c);
         break;
   }
   res=secure_write(fd, out, len);
   //--free(out);
   w_free(out);
   return res; /* bytes / GETLINE_ERR / GETLINE_PIPE */
}

int writeline_format(int fd, int leading , char * fmt, ...){
   char out[4096];
   int len, res;
   va_list az;
   if (!fmt) return GETLINE_ERR;
   va_start(az,fmt);
   len=vsnprintf(out, 4090, fmt, az);
   switch (leading){
      case WRITELINE_LEADING_NONE:
         break;
      case WRITELINE_LEADING_N:
         out[len]='\n'; len++;
         break;
      case WRITELINE_LEADING_RN:
      default:
         out[len]='\r'; len++;
         out[len]='\n'; len++;
         break;
   }
   res=secure_write(fd, out, len);
   return res; /* bytes / GETLINE_ERR */
}

struct linebuf * linebuf_init(int len){
   struct linebuf * l;
   //--l=malloc(sizeof(linebuf));
   //--if (!l) return NULL;
   l=w_malloc(sizeof(linebuf));
   //--l->buf=malloc(len);
   l->buf=w_malloc(len);
   l->max=len;
   linebuf_zero(l);
   return l;
}

void linebuf_zero(struct linebuf *l){
   l->lineend=NULL;
   l->bufend=NULL;
   l->len=0;
   l->linelen=GETLINE_LINE_NULL;
   l->line=NULL;
}

void linebuf_uninit(struct linebuf *l){
   if (l==NULL) return;
   //--if (l->buf!=NULL) free(l->buf);
   //--free(l);
   if (l->buf!=NULL) w_free(l->buf);
   w_free(l);
   l=NULL;
}
