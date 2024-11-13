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
#include <sys/types.h>
#include <sys/stat.h>
#include <time.h>
#include <sys/time.h>
#include <errno.h>
#include <malloc.h>
#include <sys/un.h>
#include <sys/socket.h>
#include <stdarg.h>
#include <dirent.h>
#include <ctype.h>
#include <sys/select.h>
#include <fcntl.h>

#include "p3scan.h"

#define DEFAULT_SOCKET_PATH "/var/run"

struct configuration_t * config;

extern void * w_malloc(size_t bytes);
extern void w_free(void *f_address);

typedef unsigned long ULONG;
#define FL_GETVERSION  0x04

// ... Cfg pathnames
//#define AVP_NODE_DEFDIR   "/var/run"
typedef struct pid_ctl_st {
   char *pid;
   char *ctl;
   int  version;
} pid_ctl;

static pid_ctl kav_run [] = {
   {"AvpPid", "AvpCtl", 4},
   {"aveserver.pid", "aveserver", 5},
   { NULL, NULL, 0 }
};

int kav_version = 0;

static char *NodePid = NULL;
static char *NodeCtl = NULL;

static int  avp_fd;        // fd for log
static int  connected;     // have done connect

static struct sockaddr_un avp_socket; // AF_UNIX address of local logger

static int avp_socket_connect(struct proxycontext *p){
   if (avp_fd == -1){
      bzero((char *)&avp_socket, sizeof(avp_socket));
      avp_socket.sun_family=AF_UNIX;
      strcpy(avp_socket.sun_path, NodeCtl);
      if ((avp_fd=socket(AF_UNIX,SOCK_STREAM,0)) < 0 ){
         do_log(LOG_CRIT, "create socket error: socket() not created %s", NodeCtl);
         return -1;
      }
   }
   if (avp_fd!=-1 && connected==-1){
      do_log(LOG_DEBUG, "Trying to connect to socket");
      if (connect(avp_fd, (struct sockaddr *)(&avp_socket),sizeof(avp_socket.sun_family) + strlen(NodeCtl)) >= 0){
         int ret;
         if (kav_version==5) {
            fd_set fds;
            struct timeval timeout;
            do_log(LOG_DEBUG, "avp_socket_connect fcntling");
            ret = fcntl(avp_fd, F_SETFL, O_NONBLOCK);
            do_log(LOG_DEBUG, "avp_socket_connect fcntl=%d",ret);
            timeout.tv_sec = 1;
            timeout.tv_usec = 0;
            FD_ZERO(&fds);
            FD_SET(avp_fd, &fds);
            do_log(LOG_DEBUG, "avp_socket_connect selecting");
            ret = select(avp_fd+1,&fds,NULL,NULL,&timeout);
            do_log(LOG_DEBUG, "avp_socket_connect select=%d",ret);
            if (ret) {
               char Myres[1024];
               if ((ret=read(avp_fd,Myres,sizeof(Myres)))==-1) return -2;
               do_log(LOG_DEBUG, "Test returned: %d", ret);
               if (ret>0) do_log(LOG_DEBUG, "Test returned value: %s", Myres);
            }
         }
         connected=1;
         do_log(LOG_DEBUG, "avp_socket_connect connected to kavdaemon");
         return 0;
      }
   } else {
      do_log(LOG_DEBUG, "Already connected");
      return 0;
   }
   do_log(LOG_CRIT, "can't connect to socket %s", NodeCtl);
   return -1;
}

static void avp_socket_close(void){
   close(avp_fd);
   avp_fd=-1;
   connected=0;
   do_log(LOG_DEBUG, "avp_socket_close");
}

/* avp_sendcommand
 * return codes:
 * >=0: OK, avpd returncode
 * -1: write error
 * -2: read  error
 * -3: error
 */
static int avp_sendcommand(struct proxycontext * p,int flags, char *buftoscan, ULONG *ulFlags, ULONG* buflen, char ** virinfo){

   register int len=strlen(buftoscan);
   char *ResultBuf=NULL;
   // output the message to the local logger
   do_log(LOG_DEBUG, "write string (%s) to kavdaemon", buftoscan);
   *virinfo=NULL;

   if (write(avp_fd, buftoscan, len+1)>=0){
      int Rez;
      long uintbuf=0;
      char Myres[4096];
      int ExitCode;
      do_log(LOG_DEBUG, "Wait results:");
      if (kav_version==5) {
         char *ptr,*ptr1;
         ResultBuf=NULL;
         while (1) {
            if ((Rez=read(avp_fd,Myres,sizeof(Myres)-1))==-1) {
               if (errno==EAGAIN) continue;
               do_log(LOG_DEBUG, "Test returned: %d %s", errno,strerror(errno));
               return -2;
            }
            do_log(LOG_DEBUG, "Test returned: %d", Rez);
            Myres[Rez]='\0';
            if (Rez>0) do_log(LOG_DEBUG, "Test returned value: %s", Myres);
            ptr = Myres;
            while ((ptr-Myres)<Rez) {
               if ((ptr1 = strchr(ptr,'\r'))!=NULL) *ptr1 = '\0';
               if (ptr1[1]=='\n') *ptr1++ = '\0';
               do_log(LOG_DEBUG, "Parsing: <%s>", ptr);
               // Code for virus found
               if (strlen(ptr)>2 && ptr[2]=='2') {
                  do_log(LOG_DEBUG, "Virus found");
                  //--ResultBuf=(char*)malloc(strlen(ptr)-2);
                  ResultBuf=(char*)w_malloc(strlen(ptr)-2);
                  strcpy(ResultBuf,ptr+4);
                  *virinfo=ResultBuf;
                  return 0x004;
               }
               // Final message: XXX mesg
               if (ptr[3]==' ') {
                  do_log(LOG_DEBUG, "End of message");
                  return 0x000;
               }
               if (ptr1==NULL) break;
               ptr = ptr1+1;
            }
         }
         return 0x000;
      } else {
      if ((Rez=read(avp_fd,(char*)&uintbuf,2))==-1) return -2;
      ExitCode=(uintbuf&0xff)-0x30;
      if ((uintbuf&0x000f)!=0xf) //0x3f '?'
      do_log(LOG_DEBUG, "Test result: %x", ExitCode);
   else
      do_log(LOG_DEBUG,"Disinfect queries:");
      do_log(LOG_DEBUG, "Test result: 0x%x, flags: 0x%x",
      uintbuf & 0x00ff, uintbuf & 0xff00 );
      ResultBuf=NULL;
      if ((uintbuf&0xff00)!=0){ /* further actions */
         if ((uintbuf&0x200)!=0){ /* where disinfected file is, uninteresting for us */
            if ((Rez=read(avp_fd, (char*)buflen, sizeof(ULONG)))==-1) return -2;
            *ulFlags|=1;
         }
         if ((uintbuf&0x100)!=0){ /* we got result string to read */
            if ((Rez=read(avp_fd,(char*)&uintbuf,sizeof(ULONG)))==-1) return -2;
            do_log(LOG_DEBUG, "Result string lenght: %d", uintbuf);
            //--ResultBuf=(char*)malloc(uintbuf+1);
            ResultBuf=(char*)w_malloc(uintbuf+1);
            if(ResultBuf!=NULL){
               char *ResultStr=ResultBuf;
               ResultBuf[0]=0;
               //if((Rez=recv(avp_fd,ResultStr,uintbuf,0))==-1) return -2;
               while((uintbuf>0)&&((Rez=recv(avp_fd,ResultStr,uintbuf,0))!=0)){
                  if(Rez==-2){
                     //--free(ResultBuf);
                     w_free(ResultBuf);
                     return -2;
                  } else {
                     uintbuf-=Rez;
                     ResultStr[Rez]=0;
                     ResultStr+=Rez;
                  }
               }
            }
         }
      }
      switch (ExitCode&0x0f){
      case 8:
         do_log(LOG_WARNING, "Corrupted objects were found");
         break;
      case 7:
         do_log(LOG_WARNING, "File AvpScanner is corrupted");
         break;
      case 6:
         do_log(LOG_WARNING, "All viruses deleted");
         break;
      case 5:
         do_log(LOG_WARNING, "All viruses disinfected");
         break;
      case 4:
         do_log(LOG_WARNING, "Known viruses were detected");
         break;
      case 3:
         do_log(LOG_WARNING, "Suspicious objects were found");
         break;
      case 2:
         do_log(LOG_WARNING, "Warning");
         break;
      case 1:
         do_log(LOG_WARNING, "Virus scan was not complete");
         break;
      case 0:
         do_log(LOG_DEBUG, "No viruses were found");
         break;
      case 0xf:
         {
         do_log(LOG_CRIT, "AVPD want's to disinfect! Please tell him not to do.");
         //--free(ResultBuf);
         w_free(ResultBuf);
         return -3;
         }
      default:
         do_log(LOG_WARNING, "Error!(test result %d)", Rez);
         break;
      } /* switch ExitCode */
      switch (ExitCode&0xf0){
         case 8:
            do_log(LOG_CRIT, "Internal error: Integrity failed.");
            break;
         case 4:
            do_log(LOG_CRIT, "Internal error: Bases not found.");
            break;
      }
      do_log(LOG_DEBUG, "Found viruses: '%s'", ResultBuf);
      //if (ResultBuf!=NULL) free(ResultBuf);
      *virinfo=ResultBuf;

      return ExitCode;
      }
   } /* if write */
   return -1;
}

static int avp_scanfile(struct proxycontext * p, int flags, char * filetoscan, char ** virname){
   int rez=-1;
   char *tbuf;
   time_t now;
   int len;
   ULONG ulFlags=0,ulDiffer=0;
   char *v, *v2, *virinfo;

   if (avp_fd<0 || !connected) if (avp_socket_connect(p)!=0) return SCANNER_RET_ERR;

   // build the message
   len=strlen(filetoscan)+30;
   //--tbuf=malloc(len+1);
   tbuf=w_malloc(len+1);
   (void)time(&now);
   if (kav_version!=5) (void)snprintf(tbuf, len, "<%d>%.15s:%s", flags, ctime(&now)+4, filetoscan);
   else (void)snprintf(tbuf, len, "SCAN xmQPRSTUWabcdefghi %s\r\n", filetoscan);

   rez=avp_sendcommand(p, flags, tbuf, &ulFlags, &ulDiffer, &virinfo);
   //do_log(LOG_DEBUG, "Virinfo: '%s'", virinfo);
   switch (rez){
      case -1:
         do_log(LOG_CRIT, "Error: cannot write to kavdaemon!");
         break;
      case -2:
         do_log(LOG_CRIT, "Error: cannot read from kavdaemon!");
         break;
      case -3:
         do_log(LOG_CRIT, "Error occured during avpd conversation");
         break;
   }
   //--free(tbuf);
   w_free(tbuf);
   if (virinfo){
      /* process virinfo */
      /* format is: <filename>    infected: EICAR-Test-File */
      v=virinfo;
      /* strip trailing filename */
      if (!strncmp(v, filetoscan, strlen(filetoscan))) v+=strlen(filetoscan);
      /* strip trailing blanks */
      while (v[0] && isspace(v[0])) v++;
      /* strip trailing '[a-z]*:' (if any) */
      v2=v;
      while (v2[0] && isalnum(v2[0])) v2++;
      if (v2[0]==':') v=v2+1;
      /* strip trailing blanks */
      while (v[0] && isspace(v[0])) v++;
      /* strip leading blanks */
      while ((len=strlen(v))>0 && isspace(v[len-1])) v[len-1]='\0';
      do_log(LOG_DEBUG, "virinfo: '%s'", v);
      *virname=strdup(v);
      //--free(virinfo);
      w_free(virinfo);
   } else *virname=NULL;
   do_log(LOG_DEBUG, "avp_scanfile returned '%d'", rez);
   return rez;
}

static int init1(void){
   int i = -1, len ;
   struct stat stat_buf;
   do_log(LOG_DEBUG, "AVP Init1");
   if (strlen(NONULL(config->virusscanner))<1){
      do_log(LOG_CRIT, "no scanner was defined. we're using " DEFAULT_SOCKET_PATH);
      config->virusscanner=strdup(DEFAULT_SOCKET_PATH);
   }
   while (kav_run[++i].pid) {
      len=strlen(config->virusscanner);
      //--if (NodeCtl) free(NodeCtl);
      //--if (NodePid) free(NodePid);
      if (NodeCtl) w_free(NodeCtl);
      if (NodePid) w_free(NodePid);
      /* Build the Nodes */
      //--if ((NodeCtl=malloc(len + strlen(kav_run[i].ctl) + 10))==NULL) return -1;
      //--if ((NodePid=malloc(len + strlen(kav_run[i].pid) + 10))==NULL) return -1;
      if ((NodeCtl=w_malloc(len + strlen(kav_run[i].ctl) + 10))==NULL) return -1;
      if ((NodePid=w_malloc(len + strlen(kav_run[i].pid) + 10))==NULL) return -1;
      strncpy(NodeCtl, config->virusscanner, len + 1);
      if (config->virusscanner[len-1]!='/') strcat(NodeCtl, "/");
      strncpy(NodePid, NodeCtl, strlen(NodeCtl) + 1);
      strcat(NodeCtl, kav_run[i].ctl);
      strcat(NodePid, kav_run[i].pid);
      len=strlen(NodeCtl);
      NodeCtl[len+1]='\0';
      NodeCtl[len+2]='\0';
      do_log(LOG_DEBUG,"Trying %s %s", NodeCtl, NodePid);
      if (stat(NodeCtl, &stat_buf)==0) break;
   }
   if (kav_run[i].pid==NULL) {
      do_log(LOG_CRIT, "No KAV daemon running");
      return 1;
   }
   kav_version = kav_run[i].version;
   do_log(LOG_DEBUG, "Version: %d NoteCtl: %s NodePid: %s", kav_version, NodeCtl, NodePid);
   connected=-1;
   avp_fd=-1;

   do_log(LOG_DEBUG, "AVP Init1 Done");

   return 0;
}

static int init2(struct proxycontext *p){
   do_log(LOG_DEBUG, "AVP Init2");

   /* Connect to socket */
   if (avp_socket_connect(p)!=0) return -1;

   do_log(LOG_DEBUG, "AVP Init2 Done");

   return 0;
}

static void uninit2(struct proxycontext *p){
   avp_socket_close();
}

static int scan(struct proxycontext *p, char **virname){
   int ret;

   do_log(LOG_DEBUG, "avpd_new scanner says hello");

   ret=avp_scanfile(p, 0, p->scanthis, virname);
   do_log(LOG_DEBUG, "AVP scanner got %d",ret);
   if ((ret&0x0f)==3 || (ret&0x0f)==4) ret = SCANNER_RET_VIRUS; /* virus */
   else if (ret<0) ret=SCANNER_RET_ERR;
   else ret = SCANNER_RET_OK;

   do_log(LOG_DEBUG, "avpd_new scanner says goodbye (ReturnCode=%s)",(ret==SCANNER_RET_OK ? "OK" : (ret==SCANNER_RET_ERR ? "ERROR" : "VIRUS")));
   return ret;
}

scanner_t scanner_avpd_new = {
   "avpd_new",             /* name */
   "Kaspersky Anti-Virus 5.x Daemon",  /* description */
   &init1,                 /* init1 (once, afer startup) */
   &init2,                 /* init2 (every connection before first mail) */
   &scan,                  /* scan */
   &uninit2,               /* uninit2 */
   NULL,                   /* uninit1 */
   0                       /* dirscan */
};

