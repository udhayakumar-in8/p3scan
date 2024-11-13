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
#include <malloc.h>
#include <sys/un.h>
#include <sys/socket.h>


/* we need p3scan.h */
#include "p3scan.h"

/* place some definitions */
#define	DEFAULT_SOCKET_PATH "/var/run/xyz-scanner.sock"

extern void * w_malloc(size_t bytes);
extern void w_free(void *f_address);

/* usually we need p3scan's config, so make it global */
struct configuration_t * config;

/* if you need some globals, make them static! */
static int  connected;
struct sockaddr_un scanner_socket;

/* if you need some functions, make them static */
static int function(void){
    return 0;
}
    
/* If you need initialization, use init1 . It is called after config parsing,
 * setuid and daemonizing.  You can check the parameters (config->xxxx), set
 * defaults if nothing is given, and so on.
 * 
 * Return values:
 *   -1 : Error. Scanning will be completely disabled.
 *        No further functions (init2, scan, uninit1, uninit2) will be called
 *    0 : OK
 */
static int init1(void){
    do_log(LOG_DEBUG, "SAMPLE Init1");
    if (strlen(NONULL(config->virusscanner))<1){
      do_log(LOG_CRIT, "no scanner was defined. we're using " DEFAULT_SOCKET_PATH);
      config->virusscanner=strdup(DEFAULT_SOCKET_PATH);
    }
    do_log(LOG_DEBUG, "AVP Init1 Done");

    return 0;
}

/* If you need initialization before scanning, use init2. Init2 is called before
 * the first mail has to be scanned (not when a client only checks if he has new
 * mails).  Here you can connect for example to a socket (which makes more sense
 * then doing that in init1).
 *
 * Return values:
 *   -1 : Error. Scanning is temporarily disabled for further mails over that
 *        connection.
 *        No further functions (scan, uninit2) will be called, but uninit1.
 *    0 : OK
 */

static int init2(struct proxycontext *p){
    do_log(LOG_DEBUG, "Init2");

    /* Connect to socket */
    if (socket_connect(p)!=0) return -1;

    do_log(LOG_DEBUG, "Init2 Done");

    return 0;
}

/* if you need to uninitialize what init2 has initialized, use uninit2, which is
 * called only if init2 is set and init2 was called!
 */
static void uninit2(struct proxycontext *p){
    socket_close();
}

/* if you need to uninitialize when pop3vscan terminates, use uninit1, which is
 * called only if init1 has returned 0 OR was not set.
 */

static void uninit1(void){

}

/* now the scanner...
 * Depending on demime (can be configured by user) and dirscan (can only be set
 * below in scanner_t by you) we have to scan the mailfile, a directory or the
 * deMIMEd files.
 *
 * +--------+---------+--------------------------------------------------------+
 * | demime | dirscan |                                                        |
 * +--------+---------+--------------------------------------------------------+
 * |   0    |    0    | scan is called once, p->scanthis points to p->mailfile |
 * +--------+---------+--------------------------------------------------------+
 * |   1    |    0    | scan is called for every MIME-file                     |
 * |        |         | p->scanthis points to the actual file in maildir       |
 * +--------+---------+--------------------------------------------------------+
 * |   1    |    1    | scan is called once, p->scanthis points to maildir     |
 * +--------+---------+--------------------------------------------------------+
 * |   0    |    1    | when the user have not set dirscan, you will get       |
 * |        |         | p->scanthis pointing to mailfile                       |
 * +--------+---------+--------------------------------------------------------+
 *
 * You can set virname to a description of the virus. If scan is invoked
 * multiple times and if you should find more than one virus we append all
 * virusnames together (seperated with ' & '). virname is not malloced (it
 * wouldn't be char**).  If you can't examime the virusname set it to NULL, when
 * no virus is found you can let them untouched.
 *
 * Return Codes:
 *   SCANNER_RET_VIRUS : The file contains a virus
 *   SCANNER_RET_OK    : The file contains NO virus
 *   SCANNER_RET_ERR   : Can't say if it's a virus
 *
 * If scan is invoked multiple times, we automatically collect the returncodes,
 * that means that if one of the files has a virus, then anything else is
 * ignored (further ERRs and OKs).
 *
 */
static int scan(struct proxycontext *p, char **virname){
   int ret;
   do_log(LOG_DEBUG, "SAMPLE scanner says hello");

   ret=scanfile(p->scanthis, virname);
   if (ret==3 || ret==4) ret = SCANNER_RET_VIRUS; /* virus */
   else if (ret<0) ret=SCANNER_RET_ERR;
   else ret = SCANNER_RET_OK;

   do_log(LOG_DEBUG, "SAMPLE scanner says goodbye");
   return ret;
}

/* Tell us your name (used for scannertype) and a brief description (shown at
 * startup and in --help).  Set the functions you need, or just NULL if not (and
 * remove the above functions).  For infos about dirscan see the scan()
 * description above.
 *
 */
scanner_t scanner_sample = {
   "sample",                     /* name */
   "A sample scanner frontend",  /* description */
   &init1,                       /* init1 (once, after startup) */
   &init2,                       /* init2 (every connection before first mail) */
   &scan,                        /* scan */
   &uninit2,                     /* uninit2 */
   &uninit1,                     /* uninit1 */
   0                             /* dirscan */
};

/*
 * to tell p3scan that we exist, add scanner_sample.o to Makefile
 * (append to OBJECTS) and define scanner_sample as extern in scanner.h and
 * place them in scannerlist[]
 *
 *   That's all! Happy coding! :)
 *
 */
