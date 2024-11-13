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
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <errno.h>
#include <malloc.h>
#include <sys/un.h>
#include <sys/socket.h>
#include <stdarg.h>
#include <ctype.h>

#include "p3scan.h"

#define DEFAULT_SOCKET_PATH "/var/run/trophie"

extern void * w_malloc(size_t bytes);
extern void w_free(void *f_address);

struct configuration_t * config;

static int  trophie_fd;    // fd for log
static int  connected;     // have done connect

static struct sockaddr_un trophie_socket;	// AF_UNIX address of local logger

static int trophie_socket_connect(struct proxycontext *p){
   if (trophie_fd == -1){
      bzero((char *)&trophie_socket, sizeof(trophie_socket));
      trophie_socket.sun_family=AF_UNIX;
      strcpy(trophie_socket.sun_path, config->virusscanner);
      if ((trophie_fd=socket(AF_UNIX,SOCK_STREAM,0)) < 0 ){
         do_log(LOG_CRIT, "create socket error: socket() not created %s",
         config->virusscanner);
         return -1;
      }
    }
    if (trophie_fd!=-1 && connected==-1){
      do_log(LOG_DEBUG, "Trying to connect to socket");
      if (connect(trophie_fd, (struct sockaddr *)(&trophie_socket),
         sizeof(trophie_socket.sun_family) + strlen(config->virusscanner)) >= 0){
         connected=1;
         do_log(LOG_DEBUG, "trophie_socket_connect connected");
         return 0;
      }
   } else {
      do_log(LOG_DEBUG, "Already connected");
      return 0;
   }
   do_log(LOG_CRIT, "can't connect to socket %s", config->virusscanner);
   return -1;
}

static void trophie_socket_close(void){
   close(trophie_fd);
   trophie_fd=-1;
   connected=0;
   do_log(LOG_DEBUG, "trophie_socket_close");
}


static int trophie_scanfile(struct proxycontext * p, char * filetoscan, char ** virname){
   char *sendbuf;
   char recvbuf[512];
   int len;

   *virname=NULL;
   if(trophie_fd<0 || !connected)
   if (trophie_socket_connect(p)!=0) return SCANNER_RET_ERR;
   len=strlen(filetoscan);
   //--sendbuf=malloc(len+2);
   sendbuf=w_malloc(len+2);
   (void)snprintf(sendbuf, len+2, "%s\n", filetoscan);
    /* send filename */
   do_log(LOG_DEBUG, "Sending to socket");
   if (write(trophie_fd, sendbuf, len+1) <0){
      do_log(LOG_ALERT, "Can't write to trophie socket");
      //--free(sendbuf);
      w_free(sendbuf);
      return SCANNER_RET_ERR;
   }
   //--free(sendbuf);
   w_free(sendbuf);
   do_log(LOG_DEBUG, "OK");
   /* retrieve message */
   memset(recvbuf, 0, sizeof(recvbuf));
   if ((len = read(trophie_fd, recvbuf, sizeof(recvbuf))) > 0){
      do_log(LOG_DEBUG, "%i bytes read", len);
      if (strchr(recvbuf, '\n'))
      *strchr(recvbuf, '\n') = '\0';
      if (recvbuf[0] == '1'){
         /* virus */
         do_log(LOG_DEBUG, "it's a virus");
         *virname=strdup(recvbuf+2);
         return SCANNER_RET_VIRUS;
      } else if (!strncmp(recvbuf, "-1", 2)){
         do_log(LOG_CRIT, "Error scanning %s (error or file not found)",
         filetoscan);
         return SCANNER_RET_ERR;
      }
   } else {
      do_log(LOG_ALERT, "Can't read message to trophie socket");
      return SCANNER_RET_ERR;
   }
   return SCANNER_RET_OK;
}

static int init1(void){
   do_log(LOG_DEBUG, "Trophie Init1");
   if (strlen(NONULL(config->virusscanner))<1){
      do_log(LOG_CRIT, "no scanner was defined. we're using " DEFAULT_SOCKET_PATH);
      config->virusscanner=strdup(DEFAULT_SOCKET_PATH);
   }

   connected=-1;
   trophie_fd=-1;

   do_log(LOG_DEBUG, "Trophie Init1 Done");

   return 0;
}

static int init2(struct proxycontext *p){
   do_log(LOG_DEBUG, "Trophie Init2");

   /* Connect to socket */
   if (trophie_socket_connect(p)!=0) return -1;

   do_log(LOG_DEBUG, "Trophie Init2 Done");

   return 0;
}

static void uninit2(struct proxycontext *p){
   trophie_socket_close();
}

static int scan(struct proxycontext *p, char ** virname){
   int ret;
   do_log(LOG_DEBUG, "Trophie scanner says hello");

   ret=trophie_scanfile(p, p->scanthis, virname);

   do_log(LOG_DEBUG, "Trophie scanner says goodbye");
   return ret;
}

scanner_t scanner_trophie = {
   "trophie",                    /* name */
   "Trophie antivirus daemon (for Trend Antivirus)",  /* description */
   &init1,                       /* init1 (once, afer startup) */
   &init2,                       /* init2 (every connection before first mail) */
   &scan,                        /* scan */
   &uninit2,                     /* uninit2 */
   NULL,                         /* uninit1 */
   0                             /* dirscan */
};

