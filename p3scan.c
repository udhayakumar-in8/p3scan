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

/* List of features wanted (for grep'ing)
TODO: Verbosity
TODO: Integrity check (check directories/permissions at start)
TODO: Wanted: Header parser
TODO: Wanted: white-list support
TODO: Wanted: no iptables support
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>
#include <sys/signal.h>
#include <sys/wait.h>
#include <pwd.h>
#include <time.h>
#include <sys/time.h>
#include <syslog.h>
#include <sys/param.h>
#include <ctype.h>
#include <linux/types.h>
#include <linux/netfilter_ipv4.h>
#include <malloc.h>
#include <getopt.h>
#include <netdb.h>
#include <libgen.h>
#include <errno.h>
#include <dirent.h>
#include <sys/statvfs.h>
#include <assert.h>
#include <sys/select.h>

#include "p3scan.h"
#include "getline_ssl.h"
#include "parsefile.h"
#include "scanner.h"

#ifdef DEMIME
#include "ripmime/mime.h"
#include "ripmime/ripmime-api.h"
#endif

/* globals */
int numprocs;
struct configuration_t * config;

/* p->ismail legend:
   ismail=0 not processing a message - parsing client commands
   ismail=1 enable message parsing (got RETR/TOP) - start trapping email
   ismail=2 got "+ok", read the mail into file
   ismail=3 closed header buffer
   ismail=4 have entire message, start processing - email complete, start server noop's
   ismail=5 scanning done, send mail to client
*/

/* globals / protos */

#ifdef DEMIME
/* filecount from ripmime/mime.c */
extern int filecount;

/* MIMEH_set_outputdir() from ripmime/MIME_headers.c */
extern int MIMEH_set_outputdir(char *);
#endif

static int sockfd; /* has to be global, do_sigterm_main() want's to close them */

/* the proxycontext is global for do_sigterm_proxy().
 * no other function should use it! */
static struct proxycontext* global_p;

static int stralloc_ptr;
static char *strings[8];
static int str_tag[8];
static char smtpstr[LEN];

void do_sigterm_proxy2(int signr){

   if(config->debug) fprintf(stderr, "do_sigterm_proxy2, signal %i\n", signr);
   if (global_p == NULL){
      if(config->debug) fprintf(stderr,"already uninitialized");
      return;
   }
   if (signr != -1 && config->debug) fprintf(stderr, "ERR: We cot SIGTERM!\n"); /* sig -1 is ok */
   if (global_p->client_fd != -1) close(global_p->client_fd);
   if (global_p->server_fd != -1) close(global_p->server_fd);
   if (global_p->scannerinit==SCANNER_INIT_OK && config->scanner->uninit2){
      if(config->debug) fprintf(stderr, "calling uninit\n2");
      config->scanner->uninit2(global_p);
      if(config->debug) fprintf(stderr, "uninit2 done\n");
   }
   if(config->debug) fprintf(stderr, "Uninit context\n");
   context_uninit(global_p);
   global_p=NULL;
   if(config->debug) fprintf(stderr, "context_uninit done, exiting now\n");
   if (signr != -1) exit(1);
}

void do_log(int level, const char *fmt,...){
  char puffer[4096];
  char timenow[28];
  int abortfd=0;
  time_t now = time(NULL);
  va_list az;
#ifdef DEBUG_MEM
   struct mallinfo m=mallinfo();
#endif

   if (!config->debug && level==LOG_DEBUG) return;
   if (!config->debug && config->quiet && level==LOG_NOTICE) return;
   va_start(az,fmt);
   vsnprintf(puffer, 4000, fmt, az);
   strcpy(timenow,ctime(&now)+ 11);
   if (!config->debug){
     openlog(config->syslogname, LOGOPT, LOGFAC);
     syslog(LOG_NOTICE, "%s\n", puffer);
     closelog();
   } else {
     fflush(stdout);
     fprintf(stderr,
#ifdef DTIME
     "%.8s "
#endif
      "%s[%i]: "
#ifdef DEBUG_MEM
      "Mem: %i "
#endif
      "%s\n",
#ifdef DTIME
      timenow,
#endif
      config->syslogname, getpid(),
#ifdef DEBUG_MEM
      m.uordblks,
#endif
      puffer);
     fflush(NULL);
   }
   if (level==LOG_EMERG){
     do_log(LOG_NOTICE, "ERR: Exiting now...\n");
     fprintf(stderr, "%s\n", puffer);
     if (strlen(NONULL(config->emergency))){
        snprintf(puffer,4096,"echo '%s' | %s -s 'P3Scan Terminating!' %s", config->emergency, config->mail, config->emergcon);
        do_log(LOG_DEBUG,"echo '%s' | %s -s 'P3Scan Terminating!' %s", config->emergency, config->mail, config->emergcon);
        if (system(puffer)) fprintf(stderr,"ERR: Calling do_log!");
     }
     /* Tell main p3scan to abort */
     if ((abortfd=open(ABORTFILE, O_WRONLY | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR)) >= 0) close(abortfd);
     va_end(az);
     if (config->child) {
        do_sigterm_proxy2(1);
     }
     exit(1);
   }
   va_end(az);
   return;
}

/**
 * Code By Nathan Yocom, 2004 - For APress Book "The Definitive Guide to Linux Network Programming"
 */

void * w_malloc(size_t bytes) {
  void *memory = NULL;                                          // Store the allocated memory here
  memory_list *new_item = NULL;                                 // Our new item structure
  memory = calloc(bytes,1);                                     // Try to allocate the memory
  new_item = calloc(1,sizeof(struct memory_list));              // Then allocate memory for the list item as well
  if(memory) {                                                  // Make sure the first allocation worked
    if(new_item == NULL) {                                      // Make sure the second allocation worked
      config->emergency="Memory allocation error, no room for memory list item.";
      do_log(LOG_EMERG,"ERR: Memory allocation error, no room for memory list item.");
      return NULL; // We don't actually get here
    }
    global_memory_count += bytes + sizeof(struct memory_list);  // Increment our global byte count
    new_item->address = memory;                                 // Initialize the new item's address pointer
    new_item->size = bytes;                                     // Set the bytes parameter to the size of the buffer in ->address
    new_item->next = NULL;                                      // Start with a NULL prev and next pointer
    new_item->prev = NULL;
    if(memory_list_head) {                                      // If the list already has items
      new_item->next = memory_list_head;                        // Then we just add this item to the head of the list
      memory_list_head->prev = new_item;
      memory_list_head = new_item;
    } else {
      memory_list_head = new_item;                              // The list didn't have items, we add this as the head
    }
    return memory;                                              // Return the allocated memory
  } else {
    config->emergency="Memory allocation error, out of memory";
    do_log(LOG_EMERG,"ERR: Memory allocation error, out of memory.");  // The first allocation failed
    return NULL; // We don't actually get here
  }
}

void w_free(void *f_address, char *loc) {
  memory_list *temp = NULL,*found = NULL;                         // Temporary pointers for list manipulation

  if(f_address == NULL)                                           // Can't free nothing ;)
    return;

  for(temp=memory_list_head;temp!=NULL;temp = temp->next) {       // Walk the memory list looking for an item
    if(temp->address == f_address) {                              //   with the same address as we are asked to free
      found = temp;                                               //   and note that we have found it then
      break;                                                      //   break from the for loop to save time
    }
  }

  if(!found) {                                                    // If we haven't found it, then we shouldn't free it
    do_log(LOG_CRIT,"ERR: Unable to free memory not previously allocated: %s",loc); // Report this as an error
  }

  global_memory_count -= found->size + sizeof(struct memory_list);// Decrement our global byte count

  free(f_address);                                                // Actually free the data
                                                                  // Then remove the item from the list:
  if(found->prev)                                                 //   If there is an item previous to us
    found->prev->next = found->next;                              //      point it at the next item
  if(found->next)                                                 //   If there is an item after us
    found->next->prev = found->prev;                              //      point it at the previous item
  if(found == memory_list_head)                                   //   If we are the head of the list
    memory_list_head = found->next;                               //      move the head of the list up one

  free(found);                                                    // Now we can actually free the memory used by our item
}

void w_free_all(void) {
  memory_list *temp = NULL;

  while(memory_list_head) {
    free(memory_list_head->address);
    temp = memory_list_head->next;
    free(memory_list_head);
    memory_list_head = temp;
  }
}

void w_memory_init(void) {
  static int state = 0;           // Initialize a static variable we can use to keep state

  if(state != 0)                  // If the variable is not zero then we have already been called
    return;                       //  do nothing but return
                                  // If the variable is 0 then we have not been called before
  state = 1;                      // Note that we have now been called
  memory_list_head = NULL;        // Set the head of the memory list to NULL (no items)
  global_memory_count = 0;        // Start the memory allocation count at 0
  atexit(w_free_all);             // Register to have w_free_all() called at normal termination
}

/**
 * End code By Nathan Yocom.
 */

char *stristr(const char *string, const char *pattern){
  char *pptr, *sptr, *start;

  for (start = (char *)string; *start != NUL; start++){
    /* find start of pattern in string */
    for ( ; ((*start!=NUL) && (toupper(*start) != toupper(*pattern))); start++);
    if (NUL == *start) return NULL;
    pptr = (char *)pattern;
    sptr = (char *)start;
    while (toupper(*sptr) == toupper(*pptr)){
      sptr++;
      pptr++;
      /* if end of pattern then pattern was found */
      if (NUL == *pptr) return (start);
    }
  }
  return NULL;
}

char *substr(char *string, int start, size_t count) {
   smtpstr[0] = '\0'; /* The NUL string error return */
   if (string != NULL) {
      size_t len = strlen(string);
      if (start < 0) start = len + start;
      if (start >= 0 && start < len) {
         if (count == 0 || count > len - start) count = len - start;
         if (count < LEN) {
            strncpy(smtpstr, string + start, count);
            smtpstr[count] = 0;
         }
      }
   }
   return smtpstr;
}

int p3_mkstemp(char *template){
   /** mkstemp w/O_SYNC open

       Somehow this routine (even normal "mkstemp") turns all files
       in template dir to 0700 even though they are created 0600.
   */
   char *XXXXXX;
   size_t len;
   int fd;
   static uint64_t value;
   uint64_t random_time_bits;
   unsigned int attempts_min = 62 * 62 * 62;
   unsigned int count;

   static const char letters[] = LETTERS;
   int save_errno = errno;
   unsigned int attempts = attempts_min < TMP_MAX ? TMP_MAX : attempts_min;
   len = strlen(template);
   if (len < 6 || strcmp(&template[len - 6], "XXXXXX")) {
      errno = EINVAL;
      return -1;
   }
   XXXXXX = &template[len - 6];
   /* Get some more or less random data.  */
   random_time_bits = time(NULL);
   value += random_time_bits ^ getpid ();
   for (count = 0; count < attempts; value += 7777, ++count){
      uint64_t v = value;
      /* Fill in the random bits.  */
      XXXXXX[0] = letters[v % 62];
      v /= 62;
      XXXXXX[1] = letters[v % 62];
      v /= 62;
      XXXXXX[2] = letters[v % 62];
      v /= 62;
      XXXXXX[3] = letters[v % 62];
      v /= 62;
      XXXXXX[4] = letters[v % 62];
      v /= 62;
      XXXXXX[5] = letters[v % 62];
      fd=open(template, O_RDWR | O_CREAT | O_EXCL | O_SYNC, S_IRUSR | S_IWUSR);
      if (fd >= 0){
         errno = save_errno;
         return fd;
      } else if (errno != EEXIST) return -1;
   }
   /* We got out of the loop because we ran out of combinations to try.  */
   errno = EEXIST;
   return -1;
}

char *stralloc(size_t length){
   register int i;

   if (UINT_MAX == length) return NULL;      /* Assume size_t == unsigned int    */

   i = stralloc_ptr++;
   ++length;                     /* Allow for terminating NUL        */

   if ((!strings[i]) || (length > strlen(strings[i]))){
      strings[i] = (char *)realloc(strings[i], length);
      assert(NULL != strings[i]);
      str_tag[i] = -1;
   } else  str_tag[i] = 0;
   stralloc_ptr &= 7;
   return (strings[i]);
   /* Maintains 8 strings in a circular buffer */
}

char *right(char *string, size_t i){
   char *buf;
   size_t strlength = strlen(string);

   if (i > strlength) i = strlength;
   buf = stralloc(i);
   strcpy(buf, &string[strlength-i]);
   return buf;
}

char *strreplace(char *haystack,char *needle,char *rstr){
   size_t size=strlen(haystack)-strlen(needle)+strlen(rstr)+1;
   char *p=w_malloc(size * sizeof(char));
   char *ptrp=p;
   char *newstr=haystack;
   char *match;
   char *replace;
   int i,j;

   while (*newstr){
      match=needle;
      replace=rstr;
      i=0;
      while(*newstr && *match){
         if(*newstr != *match){
            *ptrp++=*newstr++;
            match=needle;
            i=0;
         } else if(*newstr==*match){
            *ptrp++=*newstr++;
            match++;
            i++;
         }
      }
      if(i==(int)strlen(needle)){
         j=0;
         while(j<i){
            ptrp--;
            j++;
         }
         while(*replace) *ptrp++=*replace++;
      }
   }
   *ptrp='\0';
   return(p);
}

char * make_message(const char *fmt, ...) {
   /* Guess we need no more than 100 bytes. */
   int n, size = 100;
   char *msg;
   va_list ap;
   if ((msg = malloc (size)) == NULL) return NULL;
   while (1) {
      /* Try to print in the allocated space. */
      va_start(ap, fmt);
      n = vsnprintf (msg, size, fmt, ap);
      va_end(ap);
      /* If that worked, return the string. */
      if (n > -1 && n < size) return msg;
      /* Else try again with more space. */
      if (n > -1) size = n+1;   /* glibc 2.1 - precisely what is needed*/
      else size *= 2; /* glibc 2.0 - twice the old size*/
      if ((msg = realloc (msg, size)) == NULL) return NULL;
   }
}

int scan_directory(struct proxycontext *p){
   int ret, ret_all;
   DIR *dp;
   struct dirent *de;
   struct stat s;
   char *file;
   int maildirlen;
   char * virname;
#define VISIZE 1000
   char *vi;
   int vipos = 0;

   char *maildir_name = strdup(p->maildir);

   /* scan directory */
   maildirlen=strlen(p->maildir);
   if (stat (p->maildir, &s) == -1){
      context_uninit(p);
      config->emergency=make_message("%s does not exist", maildir_name);
      do_log(LOG_EMERG, "ERR: %s does not exist", maildir_name);
      return SCANNER_RET_ERR;
   }
   if (!S_ISDIR(s.st_mode)){
      context_uninit(p);
      config->emergency=make_message("%s is not a directory", maildir_name);
      do_log(LOG_EMERG, "ERR: %s is not a directory", maildir_name);
      return SCANNER_RET_ERR;
   }
   if ((dp = opendir (p->maildir)) == NULL){
      context_uninit(p);
      config->emergency=make_message("Can't open directory %s", maildir_name);
      do_log(LOG_EMERG, "ERR: Can't open directory %s", maildir_name);
      return SCANNER_RET_ERR;
   }
   vi=w_malloc(VISIZE);
   ret_all=SCANNER_RET_OK;
   vi[0]='\0';
   while ((de = readdir (dp)) != NULL){
      if (strcmp (de->d_name, ".") == 0) continue;
      if (strcmp (de->d_name, "..") == 0) continue;
      file=w_malloc(maildirlen + strlen(de->d_name) +2);
      sprintf(file, "%s/%s", p->maildir, de->d_name);
      if (lstat (file, &s) == -1){
         context_uninit(p);
         w_free(file,"file1");
         config->emergency=make_message("Can't get file info for %s - I won't touch it.", file);
         do_log(LOG_EMERG, "ERR: Can't get file info for %s - I won't touch it.", file);
         continue;
      }
      if (!S_ISREG(s.st_mode)){
         context_uninit(p);
         config->emergency=make_message("%s is not a regular file. I won't touch it.", file);
         do_log(LOG_EMERG, "ERR: %s is not a regular file. I won't touch it.", file);
         w_free(file,"file2");
         continue;
      }
      /* build filename */
      do_log(LOG_DEBUG, "Going to scan '%s'", file);

      p->scanthis=file;
      virname=NULL;
      ret=config->scanner->scan(p, &virname);

      if (ret==SCANNER_RET_VIRUS){
         ret_all=SCANNER_RET_VIRUS;
         if (virname && strlen(virname)<VISIZE - vipos - 4){
            strcat(&vi[vipos], virname);
            vipos+=strlen(virname);
            strcat(vi, " & ");
            vipos+=3;
         }
      } else if (ret == SCANNER_RET_ERR && ret_all != SCANNER_RET_VIRUS) ret_all = SCANNER_RET_ERR;
      do_log(LOG_DEBUG, "Finished scanning '%s'(%s=%s)", file,(virname ? virname : "none"),(ret_all==SCANNER_RET_OK ? "OK" : (ret_all==SCANNER_RET_VIRUS ? "VIRUS" : "ERROR")));
      if (virname) w_free(virname,"virname");
      w_free(file,"file3");
   }
   closedir (dp);
   if (vipos>4){
      vi[vipos-3]='\0';
      p->virinfo=vi;
   } else p->virinfo=NULL;
   return ret_all;
}

/* clean_child_directory -- iterate through directory
 *                          removing all files and subdirectories
 *
 * args:
 * childpid -- used to construct directory path
 *             to erase. If called by child pass
 *             getpid()
 *
 * returns:
 * 0 -- OK
 * 1 -- mem allocation error
 *
 * note: do_log(LOG_EMERG, ...) currently
 * doesn't return!!!
 */
int clean_child_directory(pid_t childpid){
   DIR           *dp;
   struct dirent *de;
   char          *dir,*file;
   int           dirlen,filelen;

   dirlen=strlen(config->virusdirbase)+20;
   dir=w_malloc(dirlen);
   snprintf(dir, dirlen, "%s/children/%d/", config->virusdirbase, childpid);
   /* Erase directory if it exists */
   if ((dp = opendir (dir)) != NULL){
      do_log(LOG_DEBUG, "Erasing %s contents", dir);
      while ((de = readdir (dp)) != NULL){
         if (strcmp (de->d_name, ".") == 0) continue;
         if (strcmp (de->d_name, "..") == 0) continue;
         filelen=dirlen + strlen(de->d_name) + 2;
         file=w_malloc(filelen);
         snprintf(file, filelen, "%s%s", dir, de->d_name);
         do_log(LOG_DEBUG, "Unlinking (%s)", file);
         if ((unlink(file)<0)){
            do_log(LOG_CRIT, "ERR: File Error! Could not erase %s",file);
            return 1;
         }
         w_free(file,"file4");
      }
      closedir (dp);
      do_log(LOG_DEBUG, "Removing directory %s", dir);
      if ((rmdir(dir)<0)){
         do_log(LOG_CRIT, "ERR: Directory Error! Could not erase %s",dir);
         return 1;
      }
   }
   w_free(dir,"dir");
   return 0;
}

int checktimeout(struct proxycontext *p){
   int readerr=0, senterr=0;
   char svrout[1];

   if (p->cksmtp) return 0;
   if (config->enabletop){
      if (p->topping && p->posttop) return 0;
   }
   if (p->now+config->timeout<time(NULL)){
      if (p->ismail != 5){ // Are we sending message to client?
         if (config->broken){
            /* Line parsing */
            if (!p->gobogus) readerr=getlinep3(p->header_fd,p->hdrbuf);
            if (readerr>=0 && !p->gobogus){
               senterr=writeline(p->client_fd, WRITELINE_LEADING_RN, p->hdrbuf->line);
               if (senterr < 0) return senterr;
               do_log(LOG_DEBUG, "Timeout: Sent client a line: %s", p->hdrbuf->line);
               p->hdroffset++;
            }else{
               /* End of hdrbuf! We are still parsing! */
               if (!p->gobogus) p->gobogus=1;
               senterr=writeline(p->client_fd, WRITELINE_LEADING_RN, BOGUSX);
               if (senterr < 0) return senterr;
               do_log(LOG_DEBUG, "Timeout: Sent client a bogus line.");
            }
         } else {
            /* Character parsing */
            if (!p->gobogus) readerr=read(p->header_fd,p->cbuff,1);
            if (readerr>=0 && !p->gobogus){
               senterr=secure_write(p->client_fd,p->cbuff,1);
               if (senterr < 0) return senterr;
               do_log(LOG_DEBUG, "Timeout: Sent client a character: %s",p->cbuff);
               p->hdroffset++;
            }else{
               /* End of hdrbuff! We are still parsing! */
               p->gobogus=1;
               if (p->boguspos < 74){
                  svrout[0]=BOGUSX[p->boguspos];
                  senterr=secure_write(p->client_fd,svrout,1);
                  if (senterr < 0) return senterr;
                  do_log(LOG_DEBUG, "Timeout: Sent client a character: %s",svrout);
                  p->boguspos++;
               }else{
                  if (p->boguspos < 422){
                     senterr=secure_write(p->client_fd,PERIOD,1);
                     if (senterr < 0) return senterr;
                     p->boguspos++;
                  }else{
                     senterr=writeline(p->client_fd,WRITELINE_LEADING_N,PERIOD);
                     if (senterr < 0) return senterr;
                     p->boguspos=0;
                  }
               }
            }
         }
      }
      /* Only send NOOP when we are processing or sending to client*/
      if (p->ismail > 3){
         do_log(LOG_DEBUG, "Sending server a NOOP...");
         if (p->usessl) senterr=writeline_ssl(p->ssl, WRITELINE_LEADING_RN, SVRCMD);
         else senterr=writeline(p->server_fd, WRITELINE_LEADING_RN, SVRCMD);
         if (senterr < 0) return senterr;
         p->noop++;
      }
      do_log(LOG_DEBUG, "Reseting time...");
      p->now = time(NULL);
   }
   return 0;
}

int checkbuff(int fdc) {
   fd_set rfds;
   struct timeval tv;
   int retval,fdc2;

   FD_ZERO(&rfds);
   FD_SET(fdc, &rfds);
   tv.tv_sec = 0;
   tv.tv_usec = 10000;
   fdc2=fdc+1;
   retval = select(fdc2, &rfds, NULL, NULL, &tv);
   if (retval == -1) return 2;
   else if (retval) return 1;
   return 0;
}

int scan_mailfile(struct proxycontext *p){
   int ret=0, ret2=0, viret=0, fdc=0;
#ifdef DEMIME
   DIR *dp;
   struct dirent *de;
   int maildirlen=0;
   char *file;
#endif
   int spamfd=-1;
   unsigned long len=0, kbfree=0;
   char spmcmd[512];
   char newmsg[512];
   //char vnmsg[512];
#define NEWMSG "newmsg "
#define ALTMSG "vnmsg "
#define COPYMSG "/var/spool/p3scan/copymsg "
   FILE * scanner;
   static char  line[4096*16];
   struct statvfs fs;
   int htmlfd=0;

   ret=checktimeout(p);
   if (ret < 0) return SCANNER_RET_CRIT;
   /* See if we want to manipulate the virus notification message before it might be sent */
   if (config->altemail){
      len=strlen(config->virusdir)+strlen(ALTMSG);
      snprintf(p->vnmsg, len, "%s%s", config->virusdir,ALTMSG);
      len=strlen(COPYIT)+1+strlen(config->virustemplate)+1+strlen(p->vnmsg)+1;
      snprintf(spmcmd, len, "%s %s %s",COPYIT,config->virustemplate,p->vnmsg);
      if ((scanner=popen(spmcmd, "r"))==NULL){
        p->errmsg=1;
        do_log(LOG_ALERT, "ERR: Can't '%s' !!!", spmcmd);
        return SCANNER_RET_ERR;
      }
   }
   /* See if we have enough room to process the message based upon
   what the user determines is enough room in p3scan.conf
   This was already done... but it is also dynamic so check again.
   */
   if ( statvfs( config->virusdir, &fs ) == SCANNER_RET_ERR){
      p->errmsg=1;
      context_uninit(p);
      config->emergency="Unable to get available space!";
      do_log(LOG_EMERG, "ERR: Unable to get available space!");
      return SCANNER_RET_CRIT; // Should never reach here, but keep it clean. :)
   }
   if (fs.f_bsize==1024) kbfree=fs.f_bavail;
   else kbfree=fs.f_bsize * (fs.f_bavail / 1024) + fs.f_bavail%1024 * fs.f_bsize / 1024;
   if ( config->freespace != 0 && kbfree < config->freespace ){
      p->errmsg=1;
      config->emergency=make_message("Not enough space! Available space: %lu", kbfree);
      do_log(LOG_CRIT, "ERR: Not enough space! Available space: %lu", kbfree);
      return SCANNER_RET_CRIT;
   }
   /* Do we want to rename attachments? */
   if (config->renattach != NULL && !p->cksmtp){
      ret=checktimeout(p);
      if (ret < 0) return SCANNER_RET_CRIT;
      /* Only rename non-infected attachments */
      len=strlen(config->virusdir)+strlen(NEWMSG);
      snprintf(newmsg, len, "%s%s", config->virusdir,NEWMSG);
      if ((spamfd=open(newmsg,O_WRONLY | O_CREAT | O_TRUNC,  S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP))<0){
         p->errmsg=1;
         do_log(LOG_ALERT, "ERR: Can't create newmsg!");
         return SCANNER_RET_CRIT;
      }
      len=strlen(config->renattach)+strlen(" < ")+strlen(p->mailfile)+strlen(" 2>&1 ");
      snprintf(spmcmd, len, "%s < %s 2>&1", config->renattach, p->mailfile);
      if ((scanner=popen(spmcmd, "r"))==NULL){
         p->errmsg=1;
         do_log(LOG_ALERT, "ERR: Can't start renattach '%s' !!!", spmcmd);
         return SCANNER_RET_ERR;
      }
      /* call made, check timeout until data returned */
      fdc=fileno(scanner);
      ret2=checkbuff(fdc);
      if (ret2 > 1) return SCANNER_RET_CRIT;
      while (!ret2){
         ret2=checkbuff(fdc);
         if (ret2 > 1) return SCANNER_RET_CRIT;
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
      }
      while ((fgets(line, 4095, scanner))!=NULL){
         line[strlen(line)-1]='\0';
#ifdef DEBUG_SCANNING
         do_log(LOG_DEBUG, "AttachLine: '%s'", line);
#endif
         writeline(spamfd, WRITELINE_LEADING_N, line);
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
      }
      if((spamfd=close(spamfd))<0){
         p->errmsg=1;
         context_uninit(p);
         config->emergency=make_message("Can't close newmsg: %s", newmsg);
         do_log(LOG_EMERG, "ERR: Can't close newmsg: %s", newmsg);
         return SCANNER_RET_CRIT;
      }
      ret=pclose(scanner);
      len=strlen(MOVEIT)+1+strlen(newmsg)+1+strlen(p->mailfile)+1;
      snprintf(spmcmd, len, "%s %s %s",MOVEIT,newmsg,p->mailfile);
      if ((scanner=popen(spmcmd, "r"))==NULL){
         do_log(LOG_ALERT, "ERR: Can't '%s' !!!", spmcmd);
         p->errmsg=1;
         return SCANNER_RET_ERR;
      }
      ret=pclose(scanner);
   }
   /* end renattach */
   /* perform doctor work (scan for a virus) */
   ret=checktimeout(p);
   if (ret < 0) return SCANNER_RET_CRIT;
   p->virinfo=NULL;
#ifdef DEMIME
   if (config->demime){
      /* extract MIME Parts into maildir */
      do_log(LOG_DEBUG, "DeMIMEing to %s", p->maildir);
      viret = mkdir(p->maildir, S_IRWXU | S_IRGRP | S_IXGRP);
      if ((viret == -1)&&(errno != EEXIST)){
         do_log(LOG_CRIT, "ERR: Cannot create directory '%s' (%s). Can't scan mail.\n",
         p->maildir, strerror(errno));
         p->errmsg=1;
         return SCANNER_RET_CRIT;
      }
      MIMEH_set_outputdir( p->maildir );
      MIME_init();
      MIME_unpack( p->maildir, p->mailfile, 0);
      MIME_close();
      /* TODO: ripmime error checking */
      p->scanthis = p->maildir;

      /* SCAN */
      if (config->scanner->dirscan){
         /* scanner wants to scan the directory itself, so call it once */
         /* give directory name to scanner, if he want (basic) */
         do_log(LOG_DEBUG, "Invoking scanner");
         p->virinfo=NULL;
         viret=config->scanner->scan(p, &p->virinfo);
      } else {
         /* give all files to scanner
          * also connect all virusinfos to one string */
         viret=scan_directory(p);
      }
      do_log(LOG_DEBUG, "Scanner returned %i", viret);
      /* unlinking MIME-files */
      do_log(LOG_DEBUG, "Unlinking deMIMEd files", p->maildir);
      maildirlen=strlen(p->maildir);
      if ((dp = opendir (p->maildir)) == NULL){
         char *maildir_name = strdup(p->maildir);
         p->errmsg=1;
         context_uninit(p);
         config->emergency=make_message("Can't open directory %s to erase files", maildir_name);
         do_log(LOG_EMERG, "ERR: Can't open directory %s to erase files", maildir_name);
      } else {
         while ((de = readdir (dp)) != NULL){
            if (strcmp (de->d_name, ".") == 0) continue;
            if (strcmp (de->d_name, "..") == 0) continue;
            ret=checktimeout(p);
            if (ret < 0) return SCANNER_RET_CRIT;
            file=w_malloc(maildirlen + strlen(de->d_name) +2);
            sprintf(file, "%s/%s", p->maildir, de->d_name);
            if ((unlink(file)<0)){
               config->emergency=make_message("File Error! Could not erase %s",file);
               do_log(LOG_EMERG, "ERR: File Error! Could not erase %s",file);
            }
            w_free(file,"file5");
         }
         closedir (dp);
         rmdir(p->maildir);
      }
   } else { /* if config->demime */
#endif
      /* no demime */
      p->scanthis = p->mailfile;
      /* invoke configured scanner */
      do_log(LOG_DEBUG, "Invoking scanner");
      p->virinfo=NULL;
      viret=config->scanner->scan(p, &p->virinfo);
      do_log(LOG_DEBUG, "Scanner returned %i", viret);
      /* TODO: Fail on unexpected scanner return code. */
#ifdef DEMIME
   }
#endif
   if (p->virinfo){
      TRIM(p->virinfo);
   }
   ret=checktimeout(p);
   if (ret < 0) return SCANNER_RET_CRIT;

   /* Do we want to scan for spam? */
   if (config->checkspam && !config->ispam && !viret && !p->cksmtp){
      /* Ok, first, create a new message */
      do_log(LOG_DEBUG, "Checking for spam");
      len=strlen(config->virusdir)+strlen(NEWMSG);
      snprintf(newmsg, len, "%s%s", config->virusdir,NEWMSG);
      if ((spamfd=open(newmsg,O_WRONLY | O_CREAT | O_TRUNC,  S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP))<0){
         do_log(LOG_ALERT, "ERR: Can't create newmsg!");
         p->errmsg=1;
         return SCANNER_RET_CRIT;
      }
      /* First, find out if we need to replace "dspamuser" */
      if (strstr(config->spamcheck,"dspamuser")!=NULL){
         if (strlen(NONULL(p->dspamuser))) config->spamcheck=strreplace(config->spamcheck,"dspamuser",p->dspamuser);
      }
      /* Now call anti-spam program */
      len=strlen(config->spamcheck)+strlen(" < ")+strlen(p->mailfile)+strlen(" 2>&1 ");
      /* Trap output to a buffer. */
      snprintf(spmcmd, len, "%s < %s 2>&1", config->spamcheck, p->mailfile);
      if ((scanner=popen(spmcmd, "r"))==NULL){
         p->errmsg=1;
         do_log(LOG_ALERT, "ERR: Can't start spammer '%s' !!!", spmcmd);
         return SCANNER_RET_ERR;
      }
      /* call made, check timeout until data returned */
      fdc=fileno(scanner);
      ret2=checkbuff(fdc);
      if (ret2 > 1) return SCANNER_RET_CRIT;
      while (!ret2){
         ret2=checkbuff(fdc);
         if (ret2 > 1) return SCANNER_RET_CRIT;
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
      }
      while ((fgets(line, 4095, scanner))!=NULL){
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
         line[strlen(line)-1]='\0';
         /* write the buffer to our new message */
#ifdef DEBUG_SCANNING
         do_log(LOG_DEBUG, "SpammerLine: '%s'", line);
#endif
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
         if ((strncmp(line,".",1 ) == 0 && strlen(line) == 1)){
            do_log(LOG_DEBUG, "Not writing '.'");
         } else if ((strncmp(line,".\r",2) == 0 && strlen(line) == 2)){
            do_log(LOG_DEBUG, "Not writing '.'");
         } else if (strncmp(line,"..",2) == 0 && strlen(line) == 2 && strstr(config->spamcheck,"dspam")!=NULL){
            do_log(LOG_DEBUG, "Not writing dspam '..'");
         } else {
            writeline(spamfd, WRITELINE_LEADING_N, line);
         }
      }
      do_log(LOG_DEBUG, "Writing new .");
      writeline(spamfd, WRITELINE_LEADING_RN, ".");
      if((spamfd=close(spamfd))<0){
         context_uninit(p);
         config->emergency = "Can't close newmsg spamfd";
         do_log(LOG_EMERG, "ERR: Can't close newmsg spamfd");
         return SCANNER_RET_CRIT;
      }
      ret=pclose(scanner);
      /* Spam report is now in $virusdir/newmsg
      so now replace original msg with newmsg */
      len=strlen(MOVEIT)+1+strlen(newmsg)+1+strlen(p->mailfile)+1;
      snprintf(spmcmd, len, "%s %s %s",MOVEIT,newmsg,p->mailfile);
      if ((scanner=popen(spmcmd, "r"))==NULL){
         p->errmsg=1;
         do_log(LOG_ALERT, "ERR: Can't '%s' !!!", spmcmd);
         return SCANNER_RET_ERR;
      }
      ret=pclose(scanner);
   }
   /* End of spam checking */

   /* Start HTML parsing */
   if (config->overwrite && !viret && !p->cksmtp){
      do_log(LOG_DEBUG,"HTML Parsing now...");
      ret=checktimeout(p);
      if (ret < 0) return SCANNER_RET_CRIT;
      /* Do not parse infected mail as client will not see it anyway. */
      len=strlen(config->virusdir)+strlen(NEWMSG);
      snprintf(newmsg, len, "%s%s", config->virusdir,NEWMSG);
      if ((htmlfd=open(newmsg,O_WRONLY | O_CREAT | O_TRUNC,  S_IRUSR | S_IWUSR |S_IRGRP | S_IWGRP))<0){
         p->errmsg=1;
         do_log(LOG_ALERT, "ERR: Can't create newmsg!");
         return SCANNER_RET_CRIT;
      }
      /* First, find out if we need to replace "htmluser" */
      if (strstr(config->overwrite,"htmluser")!=NULL){
         config->overwrite=strreplace(config->overwrite,"htmluser",p->dspamuser);
      }
      /* Now call HTML Parsing program */
      len=strlen(config->overwrite)+strlen(" < ")+strlen(p->mailfile)+strlen(" 2>&1 ");
      /* Trap parser program output to a buffer. */
      snprintf(spmcmd, len, "%s < %s 2>&1", config->overwrite, p->mailfile);
      if ((scanner=popen(spmcmd, "r"))==NULL){
         p->errmsg=1;
         do_log(LOG_ALERT, "ERR: Can't start HTML parser '%s' !!!", spmcmd);
         return SCANNER_RET_ERR;
      }
      /* call made, check timeout until data returned */
      fdc=fileno(scanner);
      ret2=checkbuff(fdc);
      if (ret2 > 1) return SCANNER_RET_CRIT;
      while (!ret2){
         ret2=checkbuff(fdc);
         if (ret2 > 1) return SCANNER_RET_CRIT;
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
      }
      while ((fgets(line, 4095, scanner))!=NULL){
         line[strlen(line)-1]='\0';
         /* write the buffer to our new message */
#ifdef DEBUG_SCANNING
         do_log(LOG_DEBUG, "HTML Line: '%s'", line);
#endif
         writeline(htmlfd, WRITELINE_LEADING_N, line);
         ret=checktimeout(p);
         if (ret < 0) return SCANNER_RET_CRIT;
      }
      if((htmlfd=close(htmlfd))<0){
         context_uninit(p);
         sprintf(config->emergency,"Can't close newmsg htmlfd");
         do_log(LOG_EMERG, "ERR: Can't close newmsg htmlfd");
         return SCANNER_RET_CRIT;
      }
      /* See if the call worked */
      ret=pclose(scanner);

      if(ret==0){
         len=strlen(MOVEIT)+1+strlen(newmsg)+1+strlen(p->mailfile)+1;
         snprintf(spmcmd, len, "%s %s %s",MOVEIT,newmsg,p->mailfile);
         if ((scanner=popen(spmcmd, "r"))==NULL){
            p->errmsg=1;
            do_log(LOG_ALERT, "ERR: Can't '%s' !!!", spmcmd);
            return SCANNER_RET_ERR;
         }
         ret=pclose(scanner);
      } else do_log(LOG_ALERT, "ERR: HTML Parser returned error! Ignoring it's output!");
   }
   /* End HTML parsing */

   if (strlen(NONULL(p->virinfo))<1){
      if (p->virinfo) w_free(p->virinfo,"p->virinfo");
      p->virinfo=strdup(MESSAGE_NOVIRINFO);
   }
   ret=viret;
   return ret;
}

unsigned long send_mailfile(char * mailfile, int fd, struct proxycontext *p){
   struct linebuf *filebuf, *footbuf;
   int mailfd, footfd;
   int res=0, sendret=0, gotprd=0, gottxt=0, nogo=0;
   unsigned long len=0;
   char svrout[1];
   if ((mailfd=open(mailfile, O_RDONLY ))<0){
      context_uninit(p);
      config->emergency=make_message("Can't open mailfile (%s)!", mailfile);
      do_log(LOG_EMERG, "ERR: Can't open mailfile (%s)!", mailfile);
      return 0;
   }
   filebuf=linebuf_init(16384);
   footbuf=linebuf_init(512);
   if (!filebuf){
      close(mailfd);
      close(fd);
      context_uninit(p);
      config->emergency="Could not allocate memory for sending mail!";
      do_log(LOG_EMERG, "ERR: Could not allocate memory for sending mail!");
   }
   gotprd=0;
   /* advance to mailfd pointer to past data already sent: */
   if (config->broken){
      if(p->hdroffset && !p->gobogus){
         while (p->hdroffset){
            res=getlinep3(mailfd, filebuf);
            p->hdroffset--;
         }
      }
   } else {
      if(p->hdroffset){
         lseek(mailfd, p->hdroffset, SEEK_SET);
      }
      /* See if bogus headerline sent */
      if (p->gobogus){
         if (p->boguspos < 91){
            svrout[0]=BOGUSX[p->boguspos];
            secure_write(p->client_fd,svrout,1);
            p->boguspos++;
         }
         /* now close it */
         writeline(p->client_fd,WRITELINE_LEADING_RN,PERIOD);
         p->gobogus=0;
      }
   }
   while (1){
      sendret=checktimeout(p);
      if (sendret==GETLINE_PIPE){
         do_log(LOG_CRIT, "ERR: Client disappeared during mail send!");
         linebuf_uninit(filebuf);
         return EPIPE;
      } else if (sendret){
         context_uninit(p);
         linebuf_uninit(filebuf);
         config->emergency="Sending mail to client";
         do_log(LOG_EMERG, "ERR: Sending mail to client");
         /* we are dead now. Should not reach here. But allow it
         to fall through in case LOG_EMERG is changed in the future. */
         return 1;
      }
      if ((res=getlinep3(mailfd, filebuf))<0){
         if (res==GETLINE_TOO_LONG){
            /* Buffer contains part of line,
               take care of later */
         } else {
            /* Other error, take care of later */
            break;
         }
      }
      if (filebuf->linelen >=0 ){
         len += filebuf->linelen;
#ifdef DEBUG_MESSAGE
         do_log(LOG_DEBUG, ">%s", filebuf->line);
#endif
         if ((strncmp(filebuf->line,".",1 ) == 0 && strlen(filebuf->line) == 1)) gotprd=1;
         if ((strncmp(filebuf->line,".\r",2) == 0 && strlen(filebuf->line) == 2)) gotprd=1;
         //if ((strncmp(filebuf->line,"Content-Type: application/pgp-signature",39)==0 && strlen(filebuf->line)==39)) gotpgp=1;
         //if ((strncmp(filebuf->line,"Content-Type: application/pgp-signature",39)==0 && strlen(filebuf->line)==39)) nogo=1;
         if (strncmp(filebuf->line,"Content-Type: ",14)==0){
            if ((strncmp(filebuf->line,"Content-Type: text/plain;",25)==0 && strlen(filebuf->line)==25)) gottxt=1;
            else nogo=1;
         }
         if (p->cksmtp && gotprd && !nogo){
           if ((footfd=open(FOOTER,O_RDONLY))>=0){
             sendret=writeline(fd, WRITELINE_LEADING_RN, "**********");
             while(1){
               if ((sendret=getlinep3(footfd, footbuf))<0){
                  break;
               }
               if (footbuf->linelen >=0 ){
                 sendret=writeline(fd, WRITELINE_LEADING_RN, footbuf->line);
               }
             }
             close(footfd);
             writeline_format(fd, WRITELINE_LEADING_RN,PROGNAME" "VERSION" running on %s.%s", paramlist_get(p->params, "%HOSTNAME%"),paramlist_get(p->params, "%DOMAINNAME%"));
             sendret=writeline_format(fd,WRITELINE_LEADING_RN,"%s",paramlist_get(p->params,"%VDINFO%"));
             sendret=writeline(fd,WRITELINE_LEADING_RN,"**********");
           }
         }
         /* Take care of buffer here */
         if (res==GETLINE_TOO_LONG){
            sendret=writeline(fd, WRITELINE_LEADING_NONE, filebuf->line);
         } else {
           if (!p->cksmtp) sendret=writeline(fd, WRITELINE_LEADING_RN, filebuf->line);
           else if (!gotprd) sendret=writeline(fd, WRITELINE_LEADING_RN, filebuf->line);
         }
        if (sendret==GETLINE_PIPE){
           do_log(LOG_CRIT, "ERR: Client disappeared during mail send!");
           linebuf_uninit(filebuf);
           return EPIPE;
        } else if (sendret){
           context_uninit(p);
           linebuf_uninit(filebuf);
           config->emergency="Sending mail to client";
           do_log(LOG_EMERG, "ERR: Sending mail to client");
           /* we are dead now. Should not reach here. But allow it
           to fall through in case LOG_EMERG is changed in the future. */
           return 1;
        }
      }
   }
   if (res!=GETLINE_EOF){
      do_log(LOG_CRIT, "ERR: reading from mailfile %s, error code: %d", mailfile, res);
      linebuf_uninit(filebuf);
      return 1;
   }
   if (!gotprd){
      do_log(LOG_DEBUG, "Wrote new EOM.");
      writeline(fd, WRITELINE_LEADING_N, ".");
   }
   linebuf_uninit(filebuf);
   close(mailfd);
   return len;
}

void set_defaultparams(struct proxycontext * p){
   char buf[256];
   FILE * scanner;
   static char line[512], virdef[512];
   int len=0, vlen=0;
   char vcmd[512];

   gethostname(buf, 256);
   paramlist_set(p->params, "%HOSTNAME%", buf);
   if(getdomainname(buf, 256)) do_log(LOG_CRIT,"ERR: getdomainname");
   paramlist_set(p->params, "%DOMAINNAME%", buf);
   paramlist_set(p->params, "%PROGNAME%", PROGNAME);
   paramlist_set(p->params, "%VERSION%", VERSION);
   paramlist_set(p->params, "%CLIENTIP%", inet_ntoa(p->client_addr.sin_addr));
   sprintf(buf, "%i", ntohs(p->client_addr.sin_port));
   paramlist_set(p->params, "%CLIENTPORT%", buf);
   paramlist_set(p->params, "%SERVERIP%", inet_ntoa(p->server_addr.sin_addr));
   sprintf(buf, "%i", ntohs(p->server_addr.sin_port));
   paramlist_set(p->params, "%SERVERPORT%", buf);
   if (p->cksmtp) paramlist_set(p->params, "%PROTOCOL%", "SMTP");
   else if (p->usessl) paramlist_set(p->params, "%PROTOCOL%", "POP3S");
   else paramlist_set(p->params, "%PROTOCOL%", "POP3");
   if(config->footer!=NULL){
      len=strlen(config->footer);
      snprintf(vcmd, len+1, "%s 2>&1", config->footer);
      if ((scanner=popen(vcmd, "r"))==NULL){
         paramlist_set(p->params, "%VDINFO%", NULL);
         do_log(LOG_CRIT, "ERR: Can't get scanner version '%s' !!!", vcmd);
      }else{
        while ((fgets(line, 512, scanner))!=NULL){
           len=strlen(line);
           if ((len+vlen) < 512) {
             if (len > 1) strcat(&virdef[vlen],line);
             else if (line[0] != '\r' && line[0] != '\n') strcat(&virdef[vlen],line);
             else vlen--;
           }
           vlen=vlen+len;
         }
         pclose(scanner);
         if (vlen < 512) virdef[vlen-1]='\0';
         else virdef[511]='\0';
         paramlist_set(p->params, "%VDINFO%", virdef);
      }
   } else paramlist_set(p->params, "%VDINFO%", NULL);
}

void set_maildateparam(struct paramlist * params){
   char buf[256];
   int diff_hour, diff_min;
   time_t now = time(NULL);
   struct tm *tm = localtime(&now);
   struct tm local;
   struct tm *gmt;
   int len;
   memcpy(&local, tm, sizeof(struct tm));
   gmt = gmtime(&now);

   diff_min = 60*(local.tm_hour - gmt->tm_hour) + local.tm_min - gmt->tm_min;
   if (local.tm_year != gmt->tm_year) diff_min += (local.tm_year > gmt->tm_year)? 1440 : -1440;
   else if (local.tm_yday != gmt->tm_yday)
   diff_min += (local.tm_yday > gmt->tm_yday)? 1440 : -1440;
   diff_hour = diff_min/60;
   diff_min  = abs(diff_min - diff_hour*60);
   len = strftime(buf, sizeof(buf), "%a, ", &local);
   (void) sprintf(buf + len, "%02d ", local.tm_mday);
   len += strlen(buf + len);
   len += strftime(buf + len, sizeof(buf) - len, "%b %Y %H:%M:%S", &local);
   (void) sprintf(buf + len, " %+03d%02d", diff_hour, diff_min);
   paramlist_set(params, "%MAILDATE%", buf);
}

void set_paramsfrommailheader(char * mailfile, struct paramlist * params, struct proxycontext *p){
   struct linebuf *lb;
   int fd=0;
   char * c;
   if ((fd=open(mailfile, O_RDONLY ))<0) return;
   lb=linebuf_init(65535);
   while (getlinep3(fd, lb)>=0){
      if (lb->linelen >0 ){
         if (!strncasecmp(lb->line, "from: ", 6)){
            c=lb->line+6;
            TRIM(c);
            paramlist_set(params, "%MAILFROM%", c);
         } else if (!strncasecmp(lb->line, "subject: ", 9)) {
            c=lb->line+9;
            TRIM(c);
            paramlist_set(params, "%SUBJECT%", c);
         } else if (!strncasecmp(lb->line, "To: ", 4)) {
            c=lb->line+4;
            TRIM(c);
            paramlist_set(params, "%MAILTO%", c);
         } else if (!strncasecmp(lb->line, "X-RCPT-TO: ", 11)) {
            if (!paramlist_get(params, "%USERNAME%")){
               c=lb->line+11;
               TRIM(c);
               c = substr(c,1,(strlen(c)-2));
               paramlist_set(params, "%USERNAME%", c);
               if (!p->dspamuser) p->dspamuser=paramlist_get(params,"%USERNAME%");
            }
         }
      } else if (lb->linelen == 0) break; // only the header
   }
   linebuf_uninit(lb);
   close(fd);
}


void unset_paramsfrommailheader(struct paramlist * params){
   paramlist_set(params, "%MAILFROM%", NULL);
   paramlist_set(params, "%SUBJECT%", NULL);
   paramlist_set(params, "%MAILTO%", NULL);
   paramlist_set(params, "%VIRUSNAME%", NULL);
   paramlist_set(params, "%MAILFILE%", NULL);
   paramlist_set(params, "%P3SCANID%", NULL);
   paramlist_set(params, "%VDINFO%", NULL);
}

int do_virusaction(struct proxycontext * p){
   struct linebuf *ckbuf;
   char *mail=NULL, *mailx=NULL;
   char svrout[1];
   char comm[4096];
   unsigned long len;
   int readerr=0, bufferr=0, subjfd=-1, extrafd=-1;
   int ret;
   char *vnmsg         = strdup(p->vnmsg);
   char *mailfile_name = strdup(p->mailfile);
#define CHMODCMD "/bin/chmod 0600"

   if (p->cksmtp){
      do_log(LOG_WARNING,"554 %s",config->smtprset);
      writeline_format(p->client_fd, WRITELINE_LEADING_RN, "554 %s",config->smtprset);
      writeline_format(p->server_fd, WRITELINE_LEADING_RN, "RSET");
      writeline_format(p->server_fd, WRITELINE_LEADING_RN, "QUIT");
      return 0;
   }
   /* complete the header of the original message... */
   if (config->broken){
      if(p->hdroffset && !p->gobogus){
         while ((readerr=getlinep3(p->header_fd,p->hdrbuf)!=GETLINE_EOF)){
            writeline(p->client_fd, WRITELINE_LEADING_RN, p->hdrbuf->line);
         }
      } else {
         while ((readerr=read(p->header_fd,p->cbuff,1)>0)){
            if (readerr < 0){
               context_uninit(p);
               config->emergency="Could not read header file (broken)!";
               do_log(LOG_EMERG, "ERR: Could not read header file (broken)!");
            }
            bufferr=secure_write(p->client_fd,p->cbuff,1);
            if (bufferr==GETLINE_ERR) {
               context_uninit(p);
               config->emergency="Could not flush header buffer to client (broken)!";
               do_log(LOG_EMERG, "ERR: Could not flush header buffer to client (broken)!");
            }
         }
      }
   } else {
      if (p->gobogus){
         if (p->boguspos < 74){
            svrout[0]=BOGUSX[p->boguspos];
            secure_write(p->client_fd,svrout,1);
            p->boguspos++;
         }
         /* now close it */
         writeline(p->client_fd,WRITELINE_LEADING_RN,PERIOD);
         p->gobogus=0;
      }else{
         while ((readerr=read(p->header_fd,p->cbuff,1)>0)){
            if (readerr < 0){
               context_uninit(p);
               config->emergency="Could not read header file!";
               do_log(LOG_EMERG, "ERR: Could not read header file!");
            }
            if ((strncmp(p->cbuff,"\r",1)==0) || (strncmp(p->cbuff,"\n",1)==0) ) bufferr=secure_write(p->client_fd,"\r\n",2);
            else if ((strncmp(p->cbuff,"\r",1)!=0) && (strncmp(p->cbuff,"\n",1)!=0)) bufferr=secure_write(p->client_fd,p->cbuff,1);
            if (bufferr==GETLINE_ERR) {
               context_uninit(p);
               config->emergency="Could not flush header buffer to client!";
               do_log(LOG_EMERG, "ERR: Could not flush header buffer to client!");
            }
         }
      }
   }
   if (!p->hdrdate) writeline_format(p->client_fd,WRITELINE_LEADING_RN,"Date: %s", paramlist_get(p->params, "%MAILDATE%"));
   if (!p->hdrfrom) writeline_format(p->client_fd,WRITELINE_LEADING_RN,"From: %s", paramlist_get(p->params, "%MAILFROM%"));
   if (!p->hdrto) writeline_format(p->client_fd,WRITELINE_LEADING_RN,"To: %s", paramlist_get(p->params, "%MAILTO%"));
   p->hdroffset=0;
   p->extra=0;
   mail = w_malloc(strlen(p->mailfile)+10);
   if ((extrafd=open(EXTRA,O_RDONLY))>=0) {
      ckbuf=linebuf_init(128);
      if ((readerr=getlinep3(extrafd,ckbuf)!=GETLINE_EOF)){
         p->extra=1;
         mailx = w_malloc(strlen(p->mailfile)+10);
      } else do_log(LOG_NOTICE, "ERR: p3scan.extra should not be blank");
      linebuf_uninit(ckbuf);
      close(extrafd);
   }
   /* If mail is infected AND we just want to delete it, just don't move it */
   if (!config->delit){
      snprintf(comm,4096,"%s %s %s",MOVEIT,p->mailfile,config->virusdirbase);
      if(system(comm)) do_log(LOG_CRIT,"ERR: move");
      sync();
      snprintf(comm,4096,"%s %s/p3scan.*",CHMODCMD,config->virusdirbase);
      do_log(LOG_DEBUG,"Forcing all files 0600 %s",comm);
      if(system(comm)) do_log(LOG_CRIT,"ERR: chmod");
   }
   sprintf(mail, "%s/%i.mailout", config->notifydir,getpid());
   if (p->extra) sprintf(mailx, "%s/%i.extrout", config->notifydir,getpid());
   if (!config->altemail){
      subjfd = open(config->virustemplate, O_RDONLY);
      if (subjfd<0){
         w_free(mail,"mail0");
         if (p->extra) w_free(mailx,"mailx0");
         context_uninit(p);
         config->emergency=make_message("Critical error opening file '%s', Program aborted.", vnmsg);
         do_log(LOG_EMERG,"ERR: Critical error opening file '%s', Program aborted.", vnmsg);
          /* should not reach here as we are dead */
      }
      readerr=read(subjfd,comm,4096);
      /* Check for Subject line... */
      if (strncmp(comm,"Subject:",8)!=0) writeline_format(p->client_fd,WRITELINE_LEADING_RN,"Subject: %s %s",config->subject,paramlist_get(p->params, "%VIRUSNAME%"));
      close(subjfd);
   }
   if (p->extra) {
      if ((ret = parsefile(EXTRA, mailx, p->params, WRITELINE_LEADING_RN))!=0) {
         context_uninit(p);
         unlink(mail);
         w_free(mail,"mail1");
         if (p->extra) {
            unlink(mailx);
            w_free(mailx,"mailx1");
         }
         if (ret<0) {
            config->emergency=make_message("Can't open extra mail notification template %s", EXTRA);
            do_log(LOG_EMERG, "ERR: Can't open extra mail notification template %s",EXTRA);
         } else {
            config->emergency=make_message("Can't creade extra virus warning mail message %s", mailfile_name);
            do_log(LOG_EMERG, "ERR: Can't create extra virus warning mail message %s", mailfile_name);
         }
         return -1;
      }
   }
   if (config->altemail){
      if ((ret = parsefile(p->vnmsg, mail, p->params, WRITELINE_LEADING_RN))!=0) {
         context_uninit(p);
         unlink(mail);
         w_free(mail,"mail2");
         if (p->extra) {
            unlink(mailx);
            w_free(mailx,"mailx2");
         }
         if (ret<0) {
            config->emergency=make_message("Can't open alternate mail notification template %s", vnmsg);
            do_log(LOG_EMERG, "ERR: Can't open alternate mail notification template %s", vnmsg);
         } else {
            config->emergency=make_message("Can't create virus warning mail message %s", mailfile_name);
            do_log(LOG_EMERG, "ERR: Can't create virus warning mail message %s", mailfile_name);
         }
         return -1;
      }
      do_log(LOG_DEBUG,"Sending alternate virus notification: %s",p->vnmsg);
   } else {
      if ((ret = parsefile(config->virustemplate, mail, p->params, WRITELINE_LEADING_RN))!=0) {
         context_uninit(p);
         unlink(mail);
         w_free(mail,"mail3");
         if (p->extra) {
            unlink(mailx);
            w_free(mailx,"mailx3");
         }
         if (ret<0) {
            config->emergency=make_message("Can't open mail notification template %s", config->virustemplate);
            do_log(LOG_EMERG, "ERR: Can't open mail notification template %s",config->virustemplate);
         } else {
            config->emergency=make_message("Can't create virus warning mail message %s", mailfile_name);
            do_log(LOG_EMERG, "ERR: Can't create virus warning mail message %s", mailfile_name);
         }
         return -1;
      }
   }
   do_log(LOG_DEBUG, "sending new mail");
   len=send_mailfile(mail, p->client_fd,p);
   p->bytecount+=len;
   /* Send it to extra notification? */
   if (config->extra != NULL){
      if (p->extra) {
         snprintf(comm,4096,"cat %s | %s -s '[Virus] found in a mail to %s' %s", mailx, config->mail, paramlist_get(p->params, "%USERNAME%"),config->extra);
         do_log(LOG_DEBUG,"cat %s | %s -s '[Virus] found in a mail to %s' %s", mailx, config->mail, paramlist_get(p->params, "%USERNAME%"),config->extra);
         if(system(comm)) do_log(LOG_CRIT,"ERR: mailx");
         do_log(LOG_DEBUG,"Sent p3scan.extra message to %s",config->extra);
      } else {
         snprintf(comm,4096,"cat %s | %s -s '[Virus] found in a mail to %s' %s", mail, config->mail, paramlist_get(p->params, "%USERNAME%"),config->extra);
         do_log(LOG_DEBUG,"cat %s | %s -s '[Virus] found in a mail to %s' %s", mail, config->mail, paramlist_get(p->params, "%USERNAME%"),config->extra);
         if(system(comm)) do_log(LOG_CRIT,"ERR mail");
         do_log(LOG_DEBUG,"Sent copy of message to %s",config->extra);
      }
   }
   unlink(mail);
   w_free(mail,"mail4");
   if (p->extra) {
      unlink(mailx);
      w_free(mailx,"mailx4");
   }
   p->ismail=0;
   if (len>0) return 0;
   return -1;
}

struct proxycontext * context_init(void){
   struct proxycontext * p;
   p=w_malloc(sizeof(struct proxycontext));
   p->ismail=0;
   p->msgnum=0;
   p->mailcount=0;
   p->bytecount=0;
   p->socksize=sizeof(struct sockaddr_in);
   p->client_fd=-1;
   p->server_fd=-1;
   p->header_fd=-1;
   p->hdroffset=0;
   p->clientbuf=NULL;
   p->serverbuf=NULL;
   p->hdrbuf=NULL;
   p->virinfo=NULL;
   p->scanthis=NULL;
   p->scannerinit=SCANNER_INIT_NO;
   p->usessl=0;
   p->ssl=NULL;
   p->ctx=NULL;
   p->sbio=NULL;
   p->topping=0;
   p->posttop=0;
   p->dspamuser=NULL;
   p->actsvr=NULL;
   p->actport=0;
   return p;
}

void context_uninit(struct proxycontext * p){
   if (p->client_fd > 0 ) close(p->client_fd);
   if (p->header_fd > 0 ) close(p->header_fd);
   if (p->server_fd > 0 ){
      if(p->usessl) SSL_destroy_conn(p->server_fd, p->ssl, p->ctx, p->sbio);
      else close(p->server_fd);
   }
   paramlist_uninit(&p->params);
   linebuf_uninit(p->clientbuf);
   linebuf_uninit(p->serverbuf);
   if (config->broken) linebuf_uninit(p->hdrbuf);
   w_free(p,"p");
}

void closehdrfile(struct proxycontext * p){
   p->fakehdrdone=1;
   close(p->header_fd);
   p->hdroffset=0;
   p->header_fd = open(p->p3shdrfile, O_RDONLY);
   if (p->header_fd<0){
      char *p3shdrfile_name = strdup(p->p3shdrfile);
      context_uninit(p);
      config->emergency=make_message("Critical error opening file '%s', Program aborted.", p3shdrfile_name);
      do_log(LOG_EMERG,"ERR: Critical error opening file '%s', Program aborted.", p3shdrfile_name);
      /* should not reach here as we are dead */
   }
   p->now = time(NULL);
   if (!p->notified && !p->cksmtp){
      do_log(LOG_DEBUG, "Informing email client to wait...");
      writeline_format(p->client_fd, WRITELINE_LEADING_RN,"+OK P3Scan'ing...");
      p->notified=1;
   }
   p->ismail=3;
}

void do_sigterm_proxy(int signr){
   do_log(LOG_DEBUG, "do_sigterm_proxy, signal %i", signr);
   if (global_p == NULL){
      do_log(LOG_DEBUG, "already uninitialized");
      return;
   }
   if (signr != -1) do_log(LOG_CRIT, "ERR: We cot SIGTERM!"); /* sig -1 is ok */
   if (global_p->client_fd != -1) close(global_p->client_fd);
   if (global_p->server_fd != -1) close(global_p->server_fd);
   if (global_p->scannerinit==SCANNER_INIT_OK && config->scanner->uninit2){
      do_log(LOG_DEBUG, "calling uninit2");
      config->scanner->uninit2(global_p);
      do_log(LOG_DEBUG, "uninit2 done");
   }
   do_log(LOG_DEBUG, "Uninit context");
   context_uninit(global_p);
   global_p=NULL;
   do_log(LOG_DEBUG,"context_uninit done, exiting now");
   if (signr != -1) exit(1);
}

int proxy(struct proxycontext *p){
   fd_set fds_read;
   struct timeval timeout;
   int scanfd=-1;
   int error;
   int maybe_a_space; // signals a space in the keyword for setting USERNAME var
   int clientret, serverret;
   unsigned long len, smtpsze;
   char buf[64];
#ifdef SET_TOS
   int tos;
#endif
   int scannerret, ret;
   int trapdata=0, trapcapa1=0, postdata=0;
   int trapcapa2=0, trapcapa3=0;
   int smtpcmd=0;
   int smtprstlb=0;
   char *smtptr=NULL;
   char fcmd[512];
   FILE * scanner;
   static char  line[512];
   int   loc,loc2,first=1;
   char  *tmp=NULL;
   char  *tmp2=NULL;

   p->now = time(NULL);
   p->header_fd=-1;
   p->noop=0;
   p->cksmtp=0;
   p->usessl=0;

   p->server_addr.sin_family = AF_INET;
   /*
   // For testing:
   do_log(LOG_DEBUG,"Going to emergency mode...");
   config->emergency=make_message("This is a test of the Emergency Termination System: %s", config->runasuser);
   do_log(LOG_EMERG, "This is a test of the Emergency Termination System: %s", config->runasuser);
   */
   if (config->useurl){
      p->clientbuf=linebuf_init(4096);
      if (writeline(p->client_fd, WRITELINE_LEADING_RN,POK)){
         do_log(LOG_CRIT, "ERR: Can't send +OK to client!");
         return 1;
      }
      while(1){
         clientret=getlinep3(p->client_fd, p->clientbuf);
         if (clientret==GETLINE_OK){
            if (!strncasecmp(p->clientbuf->line,"user",4)){
               tmp=strchr(p->clientbuf->line,'#');
               tmp2=strchr(p->clientbuf->line,':');
               if (!tmp && !tmp2) {
                  do_log(LOG_CRIT, "Unable to find destination username#server:port separators %s", substr(p->clientbuf->line,6,strlen(p->clientbuf->line)));
                  return SCANNER_RET_ERR;
               }
               if (!tmp) {
                  do_log(LOG_CRIT, "Unable to find destination #server %s",substr(p->clientbuf->line,6,strlen(p->clientbuf->line)));
                  return SCANNER_RET_ERR;
               }
               if (!tmp2) {
                  do_log(LOG_CRIT, "Unable to find destination :port %s",substr(p->clientbuf->line,6,strlen(p->clientbuf->line)));
                  return SCANNER_RET_ERR;
               }
               loc = tmp-p->clientbuf->line;
               loc2 = tmp2-p->clientbuf->line;
               len=strlen(p->clientbuf->line);
               p->dspamuser=strdup(substr(p->clientbuf->line,5,loc-5));
               p->actsvr=strdup(substr(p->clientbuf->line,loc+1,loc2-loc-1));
               p->actport=atoi(strdup(substr(p->clientbuf->line,loc2+1,len-loc2)));
               p->server_addr.sin_port=htons(p->actport);
               p->server_host=gethostbyname(p->actsvr);
               if (p->server_host){
                  memcpy(&p->server_addr.sin_addr.s_addr, p->server_host->h_addr_list[0], p->server_host->h_length);
               } else {
                  p->server_addr.sin_addr.s_addr = inet_addr(p->actsvr);
               }
               p->clientbuf->linelen=GETLINE_LINE_NULL;
               break;
            } else {
               do_log(LOG_DEBUG,"client said: %s",p->clientbuf->line);
               if (writeline(p->client_fd, WRITELINE_LEADING_RN,"-ERR Not Identified")){
                  do_log(LOG_CRIT, "ERR: Can't send '-ERR Not Identified' to client!");
                  return 1;
               }
               do_log(LOG_DEBUG,"Told client: -ERR Not Identified");
            }
         }
      }
   } else {
      if (htonl(INADDR_ANY) == config->targetaddr.sin_addr.s_addr) {
         if (getsockopt(p->client_fd, SOL_IP, SO_ORIGINAL_DST, &p->server_addr, &p->socksize)){
            do_log(LOG_CRIT, "ERR: No IP-Conntrack-data (getsockopt failed)");
            return 1;
         }
         /* try to avoid loop */
         if (((ntohl(p->server_addr.sin_addr.s_addr) == INADDR_LOOPBACK)
         && p->server_addr.sin_port == config->addr.sin_port )
         /* src.ip == dst.ip */
         || (p->server_addr.sin_addr.s_addr == p->client_addr.sin_addr.s_addr)){
            do_log(LOG_CRIT, "ERR: Oops, that would loop!");
            return 1;
         }
      } else {
         /* non-proxy mode */
         p->server_addr.sin_addr.s_addr = config->targetaddr.sin_addr.s_addr;
         p->server_addr.sin_port = config->targetaddr.sin_port;
      }
   }
   /* open socket to 'real-server' */
   if ((p->server_fd = socket(PF_INET, SOCK_STREAM, 0)) < 0){
      do_log(LOG_CRIT, "ERR: Cannot open socket to real-server");
      return 1;
   }
#ifdef SET_TOS
   tos=SET_TOS;
   if (setsockopt(p->client_fd, IPPROTO_IP, IP_TOS, &tos, sizeof(tos))) do_log(LOG_WARNING, "Can't set TOS (incoming connection)");
   if (setsockopt(p->server_fd, IPPROTO_IP, IP_TOS, &tos, sizeof(tos))) do_log(LOG_WARNING, "Can't set TOS (outgoing connection)");
#endif
   p->serverbuf=linebuf_init(4096);
   p->params=paramlist_init();
   if (!config->useurl) p->clientbuf=linebuf_init(4096);
   /* Check connection type */
   if (ntohs(p->server_addr.sin_port)==config->smtpport){
      p->cksmtp=1;   /* Processing an SMTP message */
      p->checksmtp=1;/* We should scan it */
      do_log(LOG_NOTICE, "SMTP Connection from %s:%i", inet_ntoa(p->client_addr.sin_addr), ntohs(p->client_addr.sin_port));
   } else if(ntohs(p->server_addr.sin_port)==config->sslport){
      p->usessl=1;
      do_log(LOG_NOTICE, "POP3S Connection from %s:%i", inet_ntoa(p->client_addr.sin_addr), ntohs(p->client_addr.sin_port));
   } else {
      do_log(LOG_NOTICE, "POP3 Connection from %s:%i", inet_ntoa(p->client_addr.sin_addr), ntohs(p->client_addr.sin_port));
   }
   do_log(LOG_NOTICE, "Real-server address is %s:%i", inet_ntoa(p->server_addr.sin_addr), ntohs(p->server_addr.sin_port));
   if (p->usessl) ret=SSL_create_conn(p->server_fd, (struct sockaddr *) &p->server_addr, p->socksize, &p->ssl, &p->ctx, &p->sbio);
   else ret=connect(p->server_fd, (struct sockaddr *) &p->server_addr, p->socksize);
   if(ret) {
      do_log(LOG_CRIT, "ERR: Cannot connect to real-server: %s",inet_ntoa(p->server_addr.sin_addr));
      return 1;
   }
   set_defaultparams(p);

   /* releasing sockfd
   * it seems to work, that if the listener (our parent-PID) gots kicked
   * we can work AND another listener can bind to the port
   */
   close(sockfd);
   do_log(LOG_DEBUG, "starting mainloop");
   while (1){

      /* read from client */
      clientret=getlinep3(p->client_fd, p->clientbuf);
      if (clientret<0){
        if (clientret==GETLINE_TOO_LONG){
          do_log(LOG_DEBUG, "Line too long: Getting rest of line.");
        } else {
          do_log(LOG_DEBUG, "Closing connection (no more input from client)");
          return 0;
        }
      }
      if (clientret==GETLINE_OK){
         if ( p->cksmtp){
            if (p->ismail < 2 || p->ismail >4) do_log(LOG_DEBUG, "--> %s", p->clientbuf->line);
            else{
#ifdef DEBUG_SMTP
               do_log(LOG_DEBUG, "--> %s", p->clientbuf->line);
#endif
            }
         } else do_log(LOG_DEBUG, "--> %s", p->clientbuf->line);
      }

      /* read from server */
      if (p->usessl) serverret=getline_ssl(p->ssl, p->serverbuf);
      else serverret=getlinep3(p->server_fd, p->serverbuf);
      if (serverret<0){
            if (serverret==GETLINE_TOO_LONG){
            do_log(LOG_DEBUG, "Line too long: Getting rest of line.");
         } else {
            do_log(LOG_DEBUG, "Closing connection (no more input from server)");
            return 0;
         }
      } else {
         if (p->noop){
            if (!strncasecmp(p->serverbuf->line,POK, 3)){
               do_log(LOG_DEBUG, "%s: NOOP response. Flushed %i NOOP's", p->serverbuf->line, p->noop);
               linebuf_zero(p->serverbuf);
               p->noop=0;
            } else {
               do_log(LOG_DEBUG, "Oops, %s doesn't looks like a server's NOOP response. Waiting next...", p->serverbuf->line);
            }
         }
      }
      if (serverret==GETLINE_OK && p->serverbuf->line != NULL
#ifndef DEBUG_MESSAGE
          && (p->ismail < 2 || p->ismail > 3)// Are we processing a message?
#endif
      ) do_log(LOG_DEBUG, "<-- %s", p->serverbuf->line);
      if (config->useurl && first){
         if (serverret==GETLINE_OK && p->serverbuf->line != NULL && !strncasecmp(p->serverbuf->line,"+OK",3)) {
            do_log(LOG_DEBUG, "Not sending %s to client...", p->serverbuf->line);
            p->serverbuf->linelen=GETLINE_LINE_NULL;
            first=0;
            paramlist_set(p->params, "%USERNAME%",p->dspamuser);
            do_log(LOG_DEBUG,"--> USER %s",p->dspamuser);
            writeline_format(p->server_fd, WRITELINE_LEADING_RN,"USER %s",p->dspamuser);
            do_log(LOG_DEBUG, "..................us us us us us......................");
            do_log(LOG_DEBUG, "............and them them them them them..............");
            do_log(LOG_DEBUG, "........and after all, were only ordinary men.........");
            do_log(LOG_DEBUG, "..................me me me me me......................");
            do_log(LOG_DEBUG, "...............and you you you you you................");
            do_log(LOG_DEBUG, "god only knows, its not what we would choose, to do...");
         }
      }
      if (p->cksmtp){
         if (trapdata && !smtpcmd && !postdata){
            do_log(LOG_DEBUG, "not reading input buffers...");
         } else {
            if (clientret == GETLINE_NEED_READ && serverret == GETLINE_NEED_READ){
               FD_ZERO(&fds_read);
               FD_SET(p->client_fd, &fds_read);
               FD_SET(p->server_fd, &fds_read);
               timeout.tv_sec = 300;
               timeout.tv_usec = 0;
               if ((ret=select(p->server_fd + 1, &fds_read, NULL, NULL, &timeout))<1){
                  /* timeout */
                  do_log(LOG_DEBUG, "select returned %i", ret);
                  break;
               } else continue ;
            }
         }
      } else {
         if (clientret == GETLINE_NEED_READ && serverret == GETLINE_NEED_READ){
            FD_ZERO(&fds_read);
            FD_SET(p->client_fd, &fds_read);
            FD_SET(p->server_fd, &fds_read);
            timeout.tv_sec = 300;
            timeout.tv_usec = 0;
            if ((ret=select(p->server_fd + 1, &fds_read, NULL, NULL, &timeout))<1){
               /* timeout */
               do_log(LOG_DEBUG, "select returned %i", ret);
               break;
            } else continue ;
         }
      }

      if (p->ismail>3) p->serverbuf->line=NULL;
      if (p->clientbuf->linelen>=0 && p->ismail<2 ){ // Not processing message
         /* scan command the client sent */
         if (!strncasecmp(p->clientbuf->line,"retr", 4)){
            p->msgnum=atoi(&p->clientbuf->line[5]);
            if (p->msgnum<1){
               /* that's not ok */
               do_log(LOG_WARNING,"RETR msg %i (<1) !!!! ", p->msgnum);
               p->ismail=0;
            } else {
               do_log(LOG_DEBUG,"RETR %i (%d)", p->msgnum, config->scannerenabled);
               /* enable message parsing (only if scanner enabled) */
               if (config->scannerenabled){
                  p->ismail=1;
               }
               p->mailcount++;
            }
         } else if (!strncasecmp(p->clientbuf->line,"user",4)){
            paramlist_set(p->params, "%USERNAME%",right(p->clientbuf->line,strlen(p->clientbuf->line)-5));
            p->dspamuser=paramlist_get(p->params,"%USERNAME%");
         } else if (!strncasecmp(p->clientbuf->line,"capa",4)){
            trapcapa1=1;
            trapcapa2=1;
            trapcapa3=1;
            do_log(LOG_DEBUG,"Client checking server CAPABILITIES...");
         } else if (!strncasecmp(p->clientbuf->line,"top", 3)){
            if(config->enabletop) {
               p->msgnum=atoi(&p->clientbuf->line[4]);
               if (p->msgnum<1){
                  // that's not ok
                  do_log(LOG_WARNING,"TOP msg %i (<1) !!!! ", p->msgnum);
                  p->ismail=0;
               } else {
                  do_log(LOG_DEBUG,"TOP %i", p->msgnum);
                  // enable message parsing (only if scanner enabled)
                  if (config->scannerenabled){
                      p->ismail=1;
                      p->topping=1;
                  }
                  p->mailcount++;
               }
            } else {
               do_log(LOG_WARNING,"Ignoring client TOP request." );
               p->clientbuf->linelen=GETLINE_LINE_NULL; /* don't sent to server */
            }
         } else if (!strncasecmp(p->clientbuf->line,"mail from:", 10) && p->cksmtp){
            /* we have size of message */
            if (config->smtpsize){
               if((smtptr=stristr(p->clientbuf->line,"size="))){
                  /* we have size of message */
                  smtpsze=atoi(substr(smtptr,5,strlen(smtptr)-5)) / 1024;
                  if (smtpsze > config->smtpsize){
                     do_log(LOG_CRIT,"SMTP Message too large for scanning: %i",smtpsze);
                     p->checksmtp=0;
                     p->cksmtp=0;
                     p->ismail=0;
                     close(p->header_fd);
                     unlink(p->p3shdrfile);
                  }else do_log(LOG_DEBUG,"smtpsize=%i",smtpsze);
               }
            }
            if (p->checksmtp) smtpcmd++;
         } else if (!strncasecmp(p->clientbuf->line,"rcpt to:", 8) && p->cksmtp){
            if (p->checksmtp) smtpcmd++;
         } else if (!strncasecmp(p->clientbuf->line,"data", 4) && p->cksmtp && p->checksmtp){
            /* SMTP message being submitted */
            if (config->scannerenabled){
               p->ismail=1;
               trapdata=1; /* do not send "DATA" command to server */
               do_log(LOG_DEBUG,"intercepted DATA command. smtpcmd=%i",smtpcmd);
               p->clientbuf->linelen=GETLINE_LINE_NULL;
               smtprstlb=1;
            }
            p->mailcount++;
         } else {
            p->ismail=0;
         }
         if ((maybe_a_space = !strncasecmp(p->clientbuf->line,"apop", 4)) || !strncasecmp(p->clientbuf->line,"user", 4)){
            len=p->clientbuf->linelen -5;
            if( len >= sizeof(buf)) len=sizeof(buf)-1;
            if (len>0){
               memcpy(buf, (char *)(p->clientbuf->line)+5, len );
               buf[len]='\0';
               /* we don't want a space (surely with "apop") strtok is another choice. */
               if(maybe_a_space){
                  char *pbuf=strchr(buf,' ');
                  if(NULL != pbuf) *pbuf='\0';
               }
               TRIM(buf);
               if (strlen(NONULL(paramlist_get(p->params, "%USERNAME%")))) paramlist_set(p->params, "%USERNAME%", buf);
            } else {
               if (strlen(NONULL(paramlist_get(p->params, "%USERNAME%")))) paramlist_set(p->params, "%USERNAME%", "unknown");
            }
            do_log(LOG_NOTICE, "USER '%s'", paramlist_get(p->params, "%USERNAME%"));
            if (strlen(NONULL(p->dspamuser))) p->dspamuser=paramlist_get(p->params,"%USERNAME%");
         }
         /* write clientbuf to server_fd */
         if (p->clientbuf->linelen>=0){
            if (p->usessl) ret=writeline_ssl(p->ssl, WRITELINE_LEADING_RN, p->clientbuf->line);
            else ret=writeline(p->server_fd, WRITELINE_LEADING_RN, p->clientbuf->line);
            if (ret){
               do_log(LOG_CRIT, "ERR: Can't send to server!");
               return 1;
            }
         }
         p->clientbuf->linelen=GETLINE_LINE_NULL;
      }// Not processing message
      if (p->cksmtp && trapdata && !smtpcmd && !postdata){
         /* tell the client we will accept their smtp traffic. */
         /*
         It seems RFC2821 says we can reset (abort) a submission
               by sending RSET after a DATA, EOM event like such:
         ...
         DATA
         ...
         .
         RSET
         but in the real world, this does not seem to work.

         So, we are going to let the server hang while we are
         processing this submission. Otherwise, the smtp server will
         send a partial message to the recipient in the event we want
         to abort the sending of the message. If we find that we do not
         wish to send the messge, we can then cleanly abort it.

         This assumes the actual server would have accepted the data
         and in my eyes, is not a clean solution.
         */
         if (writeline(p->client_fd, WRITELINE_LEADING_RN,"354 "PROGNAME" "VERSION" accepting data.")){
            do_log(LOG_CRIT, "ERR: Can't send 354 to client!");
            //context_uninit(p);
            return 1;
         } else {
            do_log(LOG_DEBUG, "Sent 354 "PROGNAME" "VERSION" accepting data.");
            postdata=1;
         }
      }
      if (p->serverbuf->linelen>=0 || (trapdata && !smtpcmd)){
         if ((p->ismail==1 && !p->cksmtp) || (p->ismail==1 && p->cksmtp && !smtpcmd)){
            /* scan for answer */
            if (!strncasecmp(p->serverbuf->line,"+ok", 3) || trapdata){
               /* Set timer now because we might have parsed alot of message numbers */
               p->now = time(NULL);
               /* generate unique filename */
               len=strlen(config->virusdir)+14;
               snprintf(p->mailfile, len, "%sp3scan.XXXXXX", config->virusdir);
               snprintf(p->p3shdrfile, len, "%sp3shdr.XXXXXX", config->virusdir);
               if (( scanfd=p3_mkstemp(p->mailfile)) < 0 ){
                  char *mailfile_name = strdup(p->mailfile);
                  p->ismail=0;
                  context_uninit(p);
                  config->emergency=make_message("Critical error opening file '%s', Program aborted.", mailfile_name);
                  do_log(LOG_EMERG,"ERR: Critical error opening file '%s', Program aborted.", mailfile_name);
                  /* Should not reach here as we are dead */
               } else {
                  p->filename=right(p->mailfile,14);
                  if (( p->header_fd=p3_mkstemp(p->p3shdrfile)) < 0 ){
                     char *p3shdrfile_name = strdup(p->p3shdrfile);
                     p->ismail=0;
                     context_uninit(p);
                     config->emergency=make_message("Critical error opening file '%s', Program aborted.", p3shdrfile_name);
                     do_log(LOG_EMERG,"ERR: Critical error opening file '%s', Program aborted.", p3shdrfile_name);
                     /* Should not reach here as we are dead */
                  }
                  p->ismail=2;
                  p->header_exists=0;
                  p->fakehdrdone=0;
                  p->notified=0;
                  p->gobogus=0;
                  p->boguspos=0;
                  p->hdrdate=0;
                  p->hdrfrom=0;
                  p->hdrto=0;
                  p->errmsg=0;
                  if (!p->cksmtp){
                     p->serverbuf->linelen=GETLINE_LINE_NULL; /* don't send response */
                     if (config->broken) p->hdrbuf=linebuf_init(16384);
                  }
               }
            } else {
               do_log(LOG_DEBUG, "ismail=1, but we haven't got '+ok' so... setting p->ismail=0");
               p->ismail=0;
            }
         } else if (p->ismail>1){
            /* that means that we have to read the mail into file */
            if ((p->cksmtp && p->clientbuf->linelen == 0 && !p->header_exists) ||
               (!p->cksmtp && p->serverbuf->linelen == 0 && !p->header_exists)){
               if (p->cksmtp){
                  writeline(scanfd, WRITELINE_LEADING_N, "X-" PROGNAME ": v" VERSION " by Jack S. Lai. No outbound virus detected.");
                  writeline(p->header_fd, WRITELINE_LEADING_N, "X-" PROGNAME ": v" VERSION " by Jack S. Lai. No outbound virus detected.");
                  if(config->footer!=NULL){
                     len=strlen(config->footer);
                     snprintf(fcmd, len+1, "%s 2>&1", config->footer);
                     if ((scanner=popen(fcmd, "r"))==NULL){
                        do_log(LOG_CRIT, "ERR: Can't get scanner version '%s' !!!", fcmd);
                     }else{
                        while ((fgets(line, 512, scanner))!=NULL){
                          if (line[0] != '\r' && line[0] != '\n'){
                             line[strlen(line)-1]='\0';
                             writeline_format(scanfd, WRITELINE_LEADING_N,"X-" PROGNAME ": %s", line);
                             writeline_format(p->header_fd, WRITELINE_LEADING_N,"X-" PROGNAME ": %s", line);
                          }
                        }
                        pclose(scanner);
                     }
                  }
               } else {
                  writeline(scanfd, WRITELINE_LEADING_N, "X-" PROGNAME ": Version " VERSION " by <laitcg@cox.net>/<folke@ashberg.de>");
                  writeline(p->header_fd, WRITELINE_LEADING_N, "X-" PROGNAME ": Version " VERSION " by <laitcg@cox.net>/<folke@ashberg.de>");
               }
               p->header_exists=1;
               /* This is the first response the client gets after "RETR/TOP", so start
                  countdown timer now...
               */
               if (p->ismail < 3){
                  do_log(LOG_DEBUG,"Closing header buffer.");
                  closehdrfile(p);
               }else if (!p->cksmtp) do_log(LOG_DEBUG,"notified=%i",p->notified);
            }
            if (p->cksmtp){
               if(!strncasecmp(p->clientbuf->line,"Date:",5) && p->ismail < 3) p->hdrdate=1;
               if(!strncasecmp(p->clientbuf->line,"From:",5) && p->ismail < 3) p->hdrfrom=1;
               if(!strncasecmp(p->clientbuf->line,"To:",3) && p->ismail < 3) p->hdrto=1;
               if(strstr(p->clientbuf->line,"MIME") || strstr(p->clientbuf->line,"Content-Type") || !strncasecmp(p->clientbuf->line,"Subject:",8)){
                  if (p->ismail < 3){
                     do_log(LOG_DEBUG,"Caught MIME/Subj line, closing header buffer.");
                     closehdrfile(p);
                  }
               }
               if (clientret==GETLINE_TOO_LONG){
                  if (p->clientbuf->linelen >=0) {
                     writeline(scanfd, WRITELINE_LEADING_NONE, p->clientbuf->line);
                     if (p->ismail < 3) writeline(p->header_fd, WRITELINE_LEADING_NONE, p->clientbuf->line);
                  }
               } else {
                  if(p->clientbuf->linelen >=0){
                     writeline(scanfd, WRITELINE_LEADING_N, p->clientbuf->line);
                     if (p->ismail < 3) writeline(p->header_fd, WRITELINE_LEADING_N, p->clientbuf->line);
                  }
               }
            } else {
               if(!strncasecmp(p->serverbuf->line,"Date:",5) && p->ismail < 3) p->hdrdate=1;
               if(!strncasecmp(p->serverbuf->line,"From:",5) && p->ismail < 3) p->hdrfrom=1;
               if(!strncasecmp(p->serverbuf->line,"To:",3) && p->ismail < 3) p->hdrto=1;
               if(strstr(p->serverbuf->line,"MIME") || strstr(p->serverbuf->line,"Content-Type") || !strncasecmp(p->serverbuf->line,"Subject:",8)){
                  if (((config->scanner->name="bash")) && !strncasecmp(p->serverbuf->line,"Subject:",8)) p->serverbuf->line=strreplace(p->serverbuf->line,"'"," ");
                  if (p->ismail < 3){
                     do_log(LOG_DEBUG,"Caught MIME/Subj line, closing header buffer.");
                     closehdrfile(p);
                  }
               }
               if (serverret==GETLINE_TOO_LONG){
                  writeline(scanfd, WRITELINE_LEADING_NONE, p->serverbuf->line);
                  if (p->ismail < 3) writeline(p->header_fd, WRITELINE_LEADING_NONE, p->serverbuf->line);
               } else {
                  writeline(scanfd, WRITELINE_LEADING_N, p->serverbuf->line);
                  if (p->ismail < 3) writeline(p->header_fd, WRITELINE_LEADING_N, p->serverbuf->line);
               }
               /* check if isp already marked as spam so we don't tie up
                  anti-spam resources (Read as "SLOW Perl SpamAssassin!" :)
                  For example cox.net marks spam as "-- Spam --".
               */
               if (config->ispspam != NULL && strstr(p->serverbuf->line,config->ispspam)!=NULL) config->ispam=1;
                  /* Here is where we start feeding the client part of our header buffer
                     until the message has been processed */
               error=checktimeout(p);
               if (error < 0) do_log(LOG_CRIT,"ERR: Writing to client!");
            }
            if ((p->clientbuf->linelen==1 && p->clientbuf->line[0]=='.') || (p->serverbuf->linelen==1 && p->serverbuf->line[0]=='.')){
               /* mail is complete */
               error=0;
               close(scanfd);
               /* make the temp file group readable - needed when
                * virus scanner is not running as the same user as
                * p3scan */
               if (chmod(p->mailfile, S_IRUSR | S_IWUSR | S_IRGRP) < 0) {
                   do_log(LOG_WARNING,
                           "Unable to make file '%s' group readable",
                           p->mailfile);
               }
               do_log(LOG_DEBUG, "got '.\\r\\n', mail is complete.");
               if (p->ismail==2) closehdrfile(p);
               p->ismail=4;
               /* initialize the scanner before scanning the first mail
                  but only if scanning is enabled */
               if (config->scannerenabled && p->scannerinit == SCANNER_INIT_NO){
                  if (config->scanner->init2){
                     if (config->scanner->init2(p)!=0){
                        context_uninit(p);
                        config->emergency="Can't initialize scanner";
                        do_log(LOG_EMERG, "ERR: Can't initialize scanner!");
                        /* Dead now. Configuration error! */
                        p->scannerinit=SCANNER_INIT_ERR;
                     }else p->scannerinit=SCANNER_INIT_OK;
                  }else p->scannerinit=SCANNER_INIT_NULL;
               }
               set_maildateparam(p->params);
               set_paramsfrommailheader(p->mailfile, p->params,p);
               /* Scan the file now */
               scannerret=SCANNER_RET_OK;
               snprintf(p->maildir, 4090, "%s.dir", p->mailfile);
               if (p->scannerinit > 0){
                  if ((scannerret=scan_mailfile(p))==SCANNER_RET_VIRUS){
                     /* virus */
                     if (p->virinfo) TRIM(p->virinfo);
                     paramlist_set(p->params, "%VIRUSNAME%", NONULL(p->virinfo));
                     paramlist_set(p->params, "%MAILFILE%", p->mailfile);
                     if (config->delit) paramlist_set(p->params, "%P3SCANID%", config->notify);
                     else paramlist_set(p->params, "%P3SCANID%", p->filename);
                     do_log(LOG_WARNING, "%s from %s:%s to %s:%s from %s to %s user: %s virus: %s file: %s",
                        paramlist_get(p->params,"%PROTOCOL%"),
                        paramlist_get(p->params,"%CLIENTIP%"), paramlist_get(p->params,"%CLIENTPORT%"),
                        paramlist_get(p->params,"%SERVERIP%"), paramlist_get(p->params,"%SERVERPORT%"),
                        paramlist_get(p->params,"%MAILFROM%"), paramlist_get(p->params,"%MAILTO%"),
                        paramlist_get(p->params,"%USERNAME%"), paramlist_get(p->params,"%VIRUSNAME%"),
                        paramlist_get(p->params,"%P3SCANID%")
                     );
                     if (do_virusaction(p)!=0){
                        if (p->cksmtp) {
                           /* Try cleaning it up again */
                           do_log(LOG_CRIT,"ERR: Virusaction failed. Sending 554 and reseting smtp data sent.");
                           writeline_format(p->client_fd, WRITELINE_LEADING_RN, "554 %s",config->smtprset);
                           do_log(LOG_DEBUG,"Sending RSET to real smtp server.");
                           writeline_format(p->server_fd, WRITELINE_LEADING_RN, "RSET");
                           writeline_format(p->server_fd, WRITELINE_LEADING_RN, "QUIT");
                        } else {
                           do_log(LOG_CRIT,"ERR: Virusaction failed. Sending -ERR and closing pop3 connection.");
                           writeline_format(p->client_fd, WRITELINE_LEADING_RN,"-ERR Message %i contains a virus (%s).", p->msgnum, paramlist_get(p->params, "%VIRUSNAME%"));
                        }
                        p->ismail=0;
                        return 1;
                     };
                     unset_paramsfrommailheader(p->params);
                     p->clientbuf->linelen=GETLINE_LINE_NULL;
                     p->serverbuf->linelen=GETLINE_LINE_NULL;
                     if (config->delit) unlink(p->mailfile);
                  } /* virus */
                  /* see if there was a critical error */
                  if (scannerret==SCANNER_RET_CRIT){
                     if (!p->errmsg) do_log(LOG_CRIT,"ERR: Writing to client!");
                     /* exact error already reported so kill the child. This
                        should get the sysadmins attention. */
                     p->ismail=0;
                     return 1;
                  }
               }else scannerret=SCANNER_RET_ERR; /* ! error */

               if (scannerret!=SCANNER_RET_VIRUS){ /* send mail if no virus */
                  if (scannerret==SCANNER_RET_ERR){
                     do_log(LOG_ALERT, "ERR: We can't say if it is a virus! So we have to give the client the mail! You should check your configuration/system");
                     context_uninit(p);
                     config->emergency="Scanner returned unexpected error code. You should check your configuration/system.";
                     do_log(LOG_EMERG, "ERR: Scanner returned unexpected error code. You should check your configuration/system.");
                     /* We are dead now. Don't let virus mails pass */
                  }
                  /* no virus  / error / scanning disabled */
                  do_log(LOG_DEBUG, "Scanning done, sending mail now.");
                  p->ismail=5;
                  if (p->cksmtp){
                     do_log(LOG_DEBUG, "Sending DATA to server.");
                     if (writeline(p->server_fd, WRITELINE_LEADING_RN, "DATA")){
                        do_log(LOG_CRIT, "ERR: Can't send DATA to server!");
                        return 1;
                     }
                     p->serverbuf->linelen=GETLINE_LINE_NULL; /* assume 354 from server */
                     do_log(LOG_DEBUG, "Sending smtp message to server.");
                     if ((len=send_mailfile(p->mailfile, p->server_fd, p))<0){
                        do_log(LOG_CRIT, "ERR: Can't submit mail! We have to quit now!");
                        p->ismail=0;
                        return 1;
                     }
                  } else {
                     if ((len=send_mailfile(p->mailfile, p->client_fd, p))<0){
                        do_log(LOG_CRIT, "ERR: Can't send mail! We have to quit now!");
                        p->ismail=0;
                        return 1;
                     }
                  }
                  do_log(LOG_DEBUG, "Sending done.");
                  p->ismail=0;
                  p->bytecount+=len;
                  p->serverbuf->linelen=GETLINE_LINE_NULL;
                  linebuf_zero(p->serverbuf);
                  trapdata=0;
                  unlink(p->mailfile); /* we do not unlink virusmails, so only here */
               }
               close(p->header_fd);
               unlink(p->p3shdrfile);
               do_log(LOG_DEBUG, "Mail action complete");
               if (config->enabletop){
                  if (p->topping) p->posttop=1;
               }
            } /* mail complete */
            p->serverbuf->linelen=GETLINE_LINE_NULL; /* don't send to client */
         } else if (trapcapa1 && !strncasecmp(p->serverbuf->line,"PIPELINING",10)){
            p->serverbuf->linelen=GETLINE_LINE_NULL; /* don't send to client */
            trapcapa1=0;
            do_log(LOG_WARNING, "Ignoring servers PIPELINING capability...");
         } else if (!config->enabletop && trapcapa2 && !strncasecmp(p->serverbuf->line,"TOP",3)){
           p->serverbuf->linelen=GETLINE_LINE_NULL; /* don't send to client */
           trapcapa2=0;
           do_log(LOG_WARNING, "Ignoring servers TOP capability...");
         } else if (trapcapa3 && !strncasecmp(p->serverbuf->line,"STLS",4)){
            p->serverbuf->linelen=GETLINE_LINE_NULL; /* don't send to client */
            trapcapa3=0;
            do_log(LOG_WARNING, "Ignoring servers STLS capability...");
         } else if (p->cksmtp && !strncasecmp(p->serverbuf->line,"250-PIPELINING",14)){
            p->serverbuf->linelen=GETLINE_LINE_NULL; /* don't send to client */
            do_log(LOG_WARNING, "Ignoring SMTP servers PIPELINING capability...");
         }
      } /* server_buf_len >0 */
      /* we are not in mail-reading mode (ismail==0) */
      if ( p->serverbuf->linelen>=0 ){
         /* write server_buf to fd */
         if (smtpcmd && !strncasecmp(p->serverbuf->line,"250", 3)) smtpcmd--;
         if (!p->cksmtp || (p->cksmtp && strncasecmp(p->serverbuf->line,"354", 3))){
            if (writeline(p->client_fd, WRITELINE_LEADING_RN, p->serverbuf->line)){
               do_log(LOG_CRIT, "ERR: Can't send to client");
               return 1;
            }
         } else if (p->cksmtp) do_log(LOG_DEBUG,"Caught servers 354");
         p->serverbuf->linelen=GETLINE_LINE_NULL;
         p->clientbuf->linelen=GETLINE_LINE_NULL;
      }
   } //end of while
   do_log(LOG_WARNING, "Connection timeout");
   do_log(LOG_DEBUG, "Child finished");
   return 0;
}

int do_sigchld_check(pid_t pid, int stat){
   int termsig = WTERMSIG(stat);

   if (numprocs>0) numprocs--;
   if (termsig){
      do_log(LOG_CRIT, "ERR: Attention: child with pid %i died with abnormal termsignal (%i)! This is probably a bug. Please report to the author. numprocs is now %i", pid, termsig, numprocs);
   }else{
      do_log(LOG_DEBUG, "waitpid: child %i died with status %i, numprocs is now %i", pid, WEXITSTATUS(stat), numprocs);
   }

   if(clean_child_directory(pid)) do_log(LOG_DEBUG, "Error cleaning child directory!");
   return 1;
}

void do_sigchld(int signr){
   pid_t pid;
   int stat;
   while ((pid=waitpid(-1, &stat, WNOHANG)) > 0){
      do_sigchld_check(pid, stat);
   }
}

void printversion(void){
   printf(
   "\n"
   PROGNAME " " VERSION "\n"
   "(C) 2003-2005 by Jack S. Lai, <laitcg@cox.net> 12/05/2003\n"
   "         and by Folke Ashberg <folke@ashberg.de>\n"
   "\n"
   );
}

/* TODO: Enable ONLY -d -f -h and -v as command line options. */
void usage(char * progname){
   int i=0;
   printversion();
   printf(
   "Usage: %s [options]\n"
   "\n"
   "where options are:\n"
   "  -a, --renattach=FILE    Specify location of renattach if wanted\n"
   "  -A, --altvnmsg          Creates a copy of 'template=FILE' for manipulation\n"
   "                          prior to use. /var/spool/p3scan/children/<pid>/vnmsg\n"
   "  -b, --bytesfree=NUM     Number (in KBytes) that should be available before we\n"
   "                          can process messages. If not enough, report it and die.\n"
   "  -B, --broken            Enable broken processing (Outlook/Outlook Express clients).\n"
   "  -c, --viruscode=N[,N]   The code(s) the scanner returns when a virus is found\n"
   "  -C, --checksize=NUM     Number (in KBytes) of the maximum smtp message size.\n"
   "  -d, --debug             Turn on debugging. See " CONFIGFILE " for recommended\n"
   "                          debug procedure.\n"
   "  -e, --extra=ADDR        Extra notification of recipient's email address\n"
   "  -E, --emailport=PORT    Port to check smtp (email) submissions on\n"
   "  -f, --configfile=FILE   Specify a configfile\n"
   "                          Default is " CONFIGFILE "\n"
   "  -F, --footer=CMD        Specify a command to get the version info of your scanner\n"
   "                          if using the smtp footer feature file" FOOTER "\n"
   "  -g, --virusregexp=RX    Specify a RegularExpression which describes where to\n"
   "                          get the name of the virus. The first substring is\n"
   "                          used, or if regexp ends with /X the X substring\n"
   "  -G  --goodcode          The codes that enable the message to be delivered without a\n"
   "                          warning. For example Kaspersky AV reports code 10 for an\n"
   "                          encrypted .zip file\n"
   "  -h, --help              Prints this text\n"
   "  -i, --ip=IP             Listen only on IP <IP>. Default: ANY\n"
   "  -I, --targetip=IP       Connect only to IP <IP>. Default: use transparent-proxy\n"
   "  -j, --justdelete        Just delete infected mail after reporting infection\n"
   "  -J, --enabletop         Allow possible broken TOP command processing\n"
   "  -k, --checkspam         Turn on Spam Checking\n"
   "  -K, --emergcon=ADDR     Emergency Contact email address to be notified in event\n"
   "                          of program termination like no disk space.\n"
   "  -l, --pidfile=FILE      Specify where to write a pid-file\n"
   "  -L, --sslport=PORT      Use SSL on connections to port <PORT>. Default %i\n"
   "  -m, --maxchilds=NUM     Allow not more then NUM childs\n"
   "  -M, --ispspam           Specify a line used by your ISP to mark Spam\n"
   "                          For example, cox.net uses -- Spam --\n"
   "  -n, --notifydir=DIR     Create notification mails in <DIR>\n"
   "                          Default: " NOTIFY_MAIL_DIR "\n"
   "                          Also used for temporary storing\n"
   "  -N, --notify            Change infected file status line\n"
   "  -o, --overwrite         Specify path to HTML parsing program executable.\n"
   "                          Default none\n"
   "  -O, --timeout=NUM       Specify seconds to use for timeout notificatino.\n"
   "  -p, --port=PORT         Listen on port <PORT>. Default: %i\n"
   "  -P, --targetport=PORT   Connect to port <PORT>. Default: %i\n"
   "                          Ignored in transparent proxy mode\n"
   "  -q, --quiet             Turn off normal reporting\n"
   "  -r, --virusdir=DIR      Save infected mails in <DIR>\n"
   "                          Default: " VIRUS_DIR "\n"
   "  -R, --smtprset          Change smtp reject message line\n"
   "  -s, --scanner=FILE      Specify the scanner. Every scannertype handles this\n"
   "                          in an other way. This could be the scanner-\n"
   "                          executable or a FIFO, Socket, ...\n"
   "  -S, --subject=TEXT      Change virus reporting subject line\n"
   "  -t, --template=FILE     Use virus-notification-template <FILE>\n"
   , basename(progname), POP3SPORT, PORT_NUMBER, PORT_NUMBER);
   printf(
   "  -T, --scannertype=T     Define which buildin scanner-frontend to use.\n\n"
   "  Supported types:\n");
   while (scannerlist[i]){
      printf("%17s: %s\n",
      scannerlist[i]->name, scannerlist[i]->descr);
      i++;
   }
   printf( "\n"
   "  -u, --user=[UID|NAME]   Run as user <UID>. Default: " RUNAS_USER "\n"
   "                          Only takes effect when started as superuser\n"
   "  -U, --useurl            Parse username for destination url instead of\n"
   "                          iptables redirect\n"
   "  -v, --version           Prints version information\n"
   "  -x, --demime            eXtract all MIME-Parts before scanning\n"
   "  -X, --xmail=FILE        Xtra notification rcpt mail pgm. Default: " XMAIL "\n"
   "  -z, --spamcheck=FILE    Specify path to Spam Checking program executable\n"
   "                          Default /usr/bin/spamc (Mail::SpamAssassin)\n"
   "\n"
   "        see " CONFIGFILE " for detailed information\n"
   "\n"
   );
}
void parseoptions(int argc, char **argv){
   long i, ii;
   char * rest;
   int error = 0;
   struct servent *port;
   int fp, res;
   struct linebuf *cf;
   char *pargv[MAX_PSEUDO_ARGV];
   int pargc;
   char *line;
   int pidfd;
   int dofree=0;

   struct option long_options[] = {
   { "renattach",    required_argument,   NULL, 'a' },
   { "altvnmsg",     no_argument,         NULL, 'A' },
   { "bytesfree",    required_argument,   NULL, 'b' },
   { "broken",       no_argument,         NULL, 'B' },
   { "viruscode",    required_argument,   NULL, 'c' },
   { "checksize",    required_argument,   NULL, 'C' },
   { "debug",        no_argument,         NULL, 'd' },
   { "extra",        required_argument,   NULL, 'e' },
   { "emailport",    required_argument,   NULL, 'E' },
   { "configfile",   required_argument,   NULL, 'f' },
   { "footer",       required_argument,   NULL, 'F' },
   { "virusregexp",  required_argument,   NULL, 'g' },
   { "goodcode",     required_argument,   NULL, 'G' },
   { "help",         no_argument,         NULL, 'h' },
   { "ip",           required_argument,   NULL, 'i' },
   { "targetip",     required_argument,   NULL, 'I' },
   { "justdelete",   no_argument,         NULL, 'j' },
   { "enabletop",    no_argument,         NULL, 'J' },
   { "checkspam",    no_argument,         NULL, 'k' },
   { "emergcon",     required_argument,   NULL, 'K' },
   { "pidfile",      required_argument,   NULL, 'l' },
   { "sslport",      required_argument,   NULL, 'L' },
   { "maxchilds",    required_argument,   NULL, 'm' },
   { "ispspam",      required_argument,   NULL, 'M' },
   { "notifydir",    required_argument,   NULL, 'n' },
   { "notify",       required_argument,   NULL, 'N' },
   { "overwrite",    required_argument,   NULL, 'o' },
   { "timeout",      required_argument,   NULL, 'O' },
   { "port",         required_argument,   NULL, 'p' },
   { "targetport",   required_argument,   NULL, 'P' },
   { "quiet",        no_argument,         NULL, 'q' },
   { "virusdir",     required_argument,   NULL, 'r' },
   { "smtprset",     required_argument,   NULL, 'R' },
   { "scanner",      required_argument,   NULL, 's' },
   { "subject",      required_argument,   NULL, 'S' },
   { "template",     required_argument,   NULL, 't' },
   { "scannertype",  required_argument,   NULL, 'T' },
   { "user",         required_argument,   NULL, 'u' },
   { "useurl",       no_argument,         NULL, 'U' },
   { "version",      no_argument,         NULL, 'v' },
#ifdef DEMIME
   { "demime",       no_argument,         NULL, 'x' },
#endif
   { "xmail",        required_argument,   NULL, 'X' },
   { "spamcheck",    required_argument,   NULL, 'z' },
   { NULL,           no_argument,         NULL, 0 }
   };
#ifdef DEMIME
   char getoptparam[] = "hvf:a:Ab:Bc:C:de:F:g:G:i:I:jJkK:l:L:m:M:n:N:o:O:p:P:qr:R:s:S:t:T:u:UxX:z:";
#else
   char getoptparam[] = "hvf:a:Ab:Bc:C:de:F:g:G:i:I:jJkK:l:L:m:M:n:N:o:O:p:P:qr:R:s:S:t:T:u:UX:z:";
#endif
   void switchoption(char opt, char * arg, char * optstr, char * where, int state){
      char *next_tok;
      switch (opt){
         case 'h':
         case 'v':
         case 'f':
            /* don't check in second run (is in the first) */
            if (state==CONFIG_STATE_CMD) return;
            /* disallow help/version/configfile in configfile */
            if (state==CONFIG_STATE_FILE){
               fprintf(stderr, "%s '%s' is not allowed in configfile!\n", where, optstr);
               error=1;
               return;
            }
         break;
         default:
         /* only check help/version/configfile for the first cmd run */
         if (state==CONFIG_STATE_CMDPRE) return;
      }

      switch (opt){
         case 'h': /* usage */
            usage(argv[0]);
            exit(0);
            break;
         case 'v': /* version */
            printversion();
            exit(0);
            break;
         case 'f': /* config (file) */
            config->configfile = arg;
            break;
         case 'F': /* footer (file) */
            config->footer = arg;
            break;
         case 'd': /* debug */
            config->debug=1;
            break;
         case 'e': /* Extra notification */
            config->extra=arg;
            break;
         case 'E': /* SMTP (email) port */
            i=strtol(arg, &rest, 10);
            if (rest && strlen(rest)>0){
               if (i>0){ /* 123abc */
                  fprintf(stderr, "%s %s isn't a valid port\n", where, arg);
                  error=1;
               }else{
                  if((port=getservbyname(arg, "tcp"))!=NULL) config->smtpport=ntohs(port->s_port);
                  else{
                     fprintf(stderr, "Port lookup for '%s/tcp' failed! Check /etc/services\n", arg);
                     error=1;
                   }
                }
            } else {
                if (i>0) config->smtpport=i;
                else {
                  fprintf(stderr, "%s Incorrect emailport portnumber\n", where);
                  error=1;
                }
            }
            break;
         case 'l': /* PID File */
            config->pidfile=arg;
            if ((pidfd=open(config->pidfile,O_RDONLY ))>=0){
               do_log(LOG_EMERG, "ERR: PID file %s exists! Aborting!",config->pidfile);
               /* Should not reach here. We are dead. */
               pidfd=close(pidfd);
               exit(0);
            }
            break;
         case 'L': /* SSL port */
            i=strtol(arg, &rest, 10);
            if (rest && strlen(rest)>0){
               if (i>0){ /* 123abc */
                  fprintf(stderr, "%s %s isn't a valid port\n", where, arg);
                  error=1;
               }else{
                  if((port=getservbyname(arg, "tcp"))!=NULL) config->sslport=ntohs(port->s_port);
                  else{
                     fprintf(stderr, "Port lookup for '%s/tcp' failed! Check /etc/services\n", arg);
                     error=1;
                  }
               }
            } else {
               if (i>0) config->sslport=i;
               else {
                  fprintf(stderr, "%s Incorrect POP3S portnumber\n", where);
                  error=1;
               }
            }
            break;
         case 'a': /* rename attachments using renattach */
            config->renattach=arg;
            break;
         case 'A': /* use alternate virus notification email */
            config->altemail=1;
            break;
         case 'r': /* virusdir */
            config->virusdirbase=arg;
            config->virusdir=config->virusdirbase;
            break;
         case 'R': /* smtp reject */
            config->smtprset=arg;
            break;
         case 'n': /* notifydir */
            config->notifydir=arg;
            break;
         case 'm': /* Max Childs */
            i=strtol(arg, &rest, 10);
            if ((rest && strlen(rest)>0) || i<1 || i>9999){
               fprintf(stderr, "%s --maxchilds has to be 1 < val < 10000\n", where);
               error=1;
            } else config->maxchilds=(int)i;
            break;
         case 'i': /* IP (to listen on) */
            if (!strcmp(arg, "0.0.0.0")){
               config->addr.sin_addr.s_addr=htonl(INADDR_ANY);
            }else if (!inet_aton(arg, &config->addr.sin_addr)){
               fprintf(stderr, "%s %s isn't a valid IP Adress\n", where, arg);
               error=1;
            }
            break;
         case 'I': /* IP (to connect) */
            if (!strcmp(arg, "0.0.0.0")){
               config->targetaddr.sin_addr.s_addr=htonl(INADDR_ANY);
            }else if (!inet_aton(arg, &config->targetaddr.sin_addr)){
               fprintf(stderr, "%s %s isn't a valid IP Adress\n", where, arg);
               error=1;
            }
            break;
         case 'o': /* overwrite (disable) HTML */
            config->overwrite=arg;
            break;
         case 'O': /* timeOut */
            i=strtol(arg, &rest, 10);
            if ((rest && strlen(rest)>0) || i<1 || i>9999){
               fprintf(stderr, "%s --timeout has to be 1 < val < 10000\n", where);
               error=1;
            } else config->timeout=(int)i;
            break;
         case 'p': /* Port */
            i=strtol(arg, &rest, 10);
            if (rest && strlen(rest)>0){
               if (i>0){ /* 123abc */
                  fprintf(stderr, "%s %s isn't a valid port\n", where, arg);
                  error=1;
               }else{
                  if((port=getservbyname(arg, "tcp"))!=NULL){
                     config->addr.sin_port=port->s_port;
                  }else{
                     fprintf(stderr, "Port lookup for '%s/tcp' failed! Check /etc/services\n", arg);
                     error=1;
                  }
               }
            }else{
               if (i>0)config->addr.sin_port=htons((int)i);
               else{
                  fprintf(stderr, "%s Incorrect POP3 portnumber\n", where);
                  error=1;
               }
            }
            break;
         case 'P': /* target Port */
            i=strtol(arg, &rest, 10);
            if (rest && strlen(rest)>0){
               if (i>0){ /* 123abc */
                  fprintf(stderr, "%s %s isn't a valid port\n", where, arg);
                  error=1;
               }else{
                  if((port=getservbyname(arg, "tcp"))!=NULL){
                     config->targetaddr.sin_port=port->s_port;
                  }else{
                     fprintf(stderr, "Port lookup for '%s/tcp' failed! Check /etc/services\n", arg);
                     error=1;
                  }
               }
            }else{
               if (i>0)config->targetaddr.sin_port=htons((int)i);
               else{
                  fprintf(stderr, "%s Incorrect target portnumber\n", where);
                  error=1;
               }
            }
            break;
         case 'q': /* quiet */
            config->quiet=1;
            break;
         case 'u': /* Run as User */
            config->runasuser=arg;
            /* getpwnam will also accept UID's, so we need no converting*/
            break;
         case 'U': /* Parse username for destination url */
            config->useurl=1;
            break;
         case 's': /* Scanner */
            config->virusscanner=arg;
            break;
         case 't': /* template */
            config->virustemplate=arg;
            break;
         case 'c': /* Virus (exit) code */
            ii = 0;
            next_tok = strtok(arg, " \t,");
            if (next_tok){
               do{
                  if (ii < MAX_VIRUS_CODES){
                     i=strtol(next_tok, &rest, 10);
                     if ( (rest && strlen(rest)>0) || i<1 || i>256){
                        fprintf(stderr, "%s --viruscode has be a list of numbers (%s)\n", where, rest);
                        error=1;
                     }else config->viruscode[ii]=(int)i;
                     ii++;
                  }
               }while ((next_tok = strtok(NULL, " \t,")) || (ii >= MAX_VIRUS_CODES));
            }
            config->viruscode[ii] = -1;
            if (ii == 0){
               fprintf(stderr, "%s --viruscode has be a list of numbers (%s)\n", where, rest);
               error=1;
            }
            break;
         case 'G': /* Good Virus (exit) code */
            ii = 0;
            next_tok = strtok(arg, " \t,");
            if (next_tok){
               do{
                  if (ii < MAX_VIRUS_CODES){
                     i=strtol(next_tok, &rest, 10);
                     if ( (rest && strlen(rest)>0) || i<1 || i>256){
                        fprintf(stderr, "%s --good viruscode has be a list of numbers (%s)\n", where, rest);
                        error=1;
                     }else config->gvcode[ii]=(int)i;
                     ii++;
                  }
               }while ((next_tok = strtok(NULL, " \t,")) || (ii >= MAX_VIRUS_CODES));
            }
            config->gvcode[ii] = -1;
            if (ii == 0){
               fprintf(stderr, "%s --good viruscode has be a list of numbers (%s)\n", where, rest);
               error=1;
            }
            break;
#ifdef DEMIME
         case 'x': /* demime */
            config->demime = 1;
            break;
#endif
         case 'X': /* Xtra notification reciept mail program */
            config->mail=arg;
            break;
         case 'T': /* scannertype */
            i=0;
            while (scannerlist[i]){
               if(!strcasecmp(arg, scannerlist[i]->name)){
                  config->scanner=scannerlist[i];
                  i=-1;
                  break;
               }
               i++;
            }
            if (i!=-1){
               fprintf(stderr, "%s scannertype '%s' is not supported", where, arg);
               error=1;
            }
            break;
         case 'g': /* virusregexp */
            config->virusregexp = arg;
            i=strlen(arg);
            if (arg[i-2]=='/' && isdigit(arg[i-1])){
               arg[i-2]='\0';
               config->virusregexpsub=arg[i-1]-'0';
            }
            break;
         case 'k': /* check for spam */
            config->checkspam=1;
            break;
         case 'K': /* emergency Kontact! */
            config->emergcon = arg;
            break;
         case 'z': /* path to spam checking executable */
            config->spamcheck = arg;
            break;
         case 'b': /* bytes free */
            i=strtol(arg, &rest, 10);
            config->freespace=(int)i;
            break;
         case 'C': /* Check SMTP size */
            i=strtol(arg, &rest, 10);
            config->smtpsize=(int)i;
            break;
         case 'j': /* justdelete */
            config->delit=1;
            break;
         case 'J': /* enabletop */
            config->enabletop=1;
            break;
         case 'B': /* broken */
            config->broken=1;
            break;
         case 'S': /* Subject line for virus notification */
            config->subject = arg;
            break;
         case 'N': /* deleted file notification */
            config->notify = arg;
            break;
         case 'M': /* ISP marked as SPAM */
            config->ispspam = arg;
            break;

         default:
            fprintf(stderr, "%s Option '%s' isn't known\n", where, optstr);
            error=1;
      }
   }/* sub function switchoption  }}} */
   void parseargs(int c, char **v, char * where, int state){
      int option, option_index = 0;
      opterr=0;
      optind=1;
      while (1){
         option = getopt_long(c, v, getoptparam,
         long_options, &option_index);
         if (option == EOF) break;
         switchoption(option, optarg, v[optind-1], where, state);
      }
      if (state != CONFIG_STATE_CMDPRE && optind < c){
         error=1;
         while (optind < c) fprintf(stderr, "%s Unknown option '%s'\n", where, v[optind++]);
      }
   }
   config=w_malloc(sizeof(struct configuration_t));
   /* set defaults for in, char* to NULL */
   config->debug=DEBUG;
   config->quiet=QUIET;
   config->overwrite=OVERWRITE;
   config->renattach=NULL;
   config->addr.sin_port=htons((int)PORT_NUMBER);
   config->targetaddr.sin_port=htons((int)PORT_NUMBER);
   config->smtpport=SMTP_PORT;
   config->maxchilds=MAX_CHILDS;
   config->viruscode[0]=VIRUS_SCANNER_VIRUSCODE;
   config->viruscode[1]=-1;
   config->gvcode[0]=0;
   config->runasuser=NULL;
   config->virusdir=NULL;
   config->virusdirbase=NULL;
   config->notifydir=NULL;
   config->virustemplate=NULL;
   config->virusscanner=NULL;
   config->demime=0;
   config->pidfile=NULL;
   config->sslport=POP3SPORT;
   config->syslogname=NULL;
   config->addr.sin_addr.s_addr=htonl(INADDR_ANY);
   config->targetaddr.sin_addr.s_addr=htonl(INADDR_ANY);
   config->scanner=NULL;
   config->virusregexp=NULL;
   config->virusregexpsub=1;
   config->checkspam=CHECKSPAM;
   config->spamcheck=SPAMCHECK;
   config->freespace=MINSPACE;
   config->delit=DELIT;
   config->broken=0;
   config->ispspam=NULL;
   config->extra=NULL;
   config->smtprset=SMTPRSET;
   config->smtpsize=0;
   config->mail=XMAIL;
   config->timeout=TIMEOUT;
   config->footer=NULL;
   config->enabletop=0;
   config->emergcon=NULL;
   config->emergency=NULL;
   /* parse line args, but for the first time only configfile/version/help */
   parseargs(argc, argv, "\t[cmdlineparm]", CONFIG_STATE_CMDPRE);
   /* parse configfile */
   if (!config->configfile){
      config->configfile=strdup(CONFIGFILE); //TODO: 24 bytes in 1 blocks are definitely lost in loss record 2 of 2
      dofree=1;
   }
   if ((fp=open(config->configfile, O_RDONLY))>=0){
      cf=linebuf_init(4096);
      pargc=1;
      pargv[0]="";
      while ((res=getlinep3(fp, cf))>=0 && pargc<MAX_PSEUDO_ARGV-1){
         if (cf->linelen > 2){
            TRIM(cf->line);
            if (cf->line[0]!='#' && cf->line[0]!=';' && !(cf->line[0]=='/' && cf->line[1]=='/') && cf->line[0]!='='){
               /* copy to pseudo argv, change
               * 'x = y' or 'x y' to 'x='
               * This code is the horror, but it seems to work */
               line=w_malloc(strlen(cf->line)+3);
               line[0]='-'; line[1]='-'; line[2]='\0';
               strcat(line, cf->line);
               pargv[pargc]=line;
               if ((i=strcspn(line, " =\t"))>1){
                  if (i<strlen(line)){
                     line[i]='\0';
                     if ((ii=strspn(line+i+1," =\t"))>=0){
                        rest=line+i+ii+1;
                        if (rest && strlen(rest)>0 ){
                           pargv[pargc][strlen(pargv[pargc])]='=';
                           memcpy(pargv[pargc]+i+1, rest, strlen(rest)+1); //TODO: Source and destination overlap in memcpy
                        }
                     }
                  }
               }
               pargc++;
            }
         }
      }
      close(fp);
      linebuf_uninit(cf);
      pargv[pargc]=NULL;
      parseargs(pargc, pargv, "\t[configfile]", CONFIG_STATE_FILE);
   }
   if(dofree) free(config->configfile);
   /* now check the rest of commandline args (higher precedence than configfile) */
   parseargs(argc, argv, "\t[cmdlineparm]", CONFIG_STATE_CMD);
   if (error){
      printf(
      "Commandline options/configfile are not ok\n"
      "try --help or RTFM to get some information\n"
      "\n"
      );
      exit(1);
   }

   /* set unset values to default */
   SETIFNULL(config->runasuser, RUNAS_USER);
   SETIFNULL(config->virusdirbase, VIRUS_DIR);
   SETIFNULL(config->virusdir, config->virusdirbase );
   SETIFNULL(config->notifydir, NOTIFY_MAIL_DIR);
   SETIFNULL(config->virustemplate, VIRUS_TEMPLATE);
   SETIFNULL(config->virusscanner, VIRUS_SCANNER);
   SETIFNULL(config->pidfile, PID_FILE);
   SETIFNULL(config->syslogname, SYSLOG_NAME);
   SETIFNULL(config->scanner, scannerlist[0]);
   SETIFNULL(config->subject, SUBJECT);
   SETIFNULL(config->notify, NOTIFY);
   SETIFNULL(config->smtprset, SMTPRSET);
   SETIFNULL(config->mail, XMAIL);
   SETIFNULL(config->emergcon, EMERGCON);
}

void do_sigterm_main(int signr){
   int ret;

   if (signr != -1 ) do_log(LOG_NOTICE, "signalled, doing cleanup");
   close(sockfd);
   if (config->scannerenabled && config->scanner->uninit1){
      do_log(LOG_DEBUG, "calling uninit1");
      config->scanner->uninit1();
      do_log(LOG_DEBUG, "uninit1 done");
   }
   if((ret=unlink(config->pidfile)!=0)) do_log(LOG_NOTICE, "ERR: Unable to remove %s", config->pidfile);
   do_log(LOG_NOTICE, PROGNAME " terminates now");
   exit(0);
}

Sigfunc * p3signal(int signo, Sigfunc *func){
   struct sigaction act, oact;

   act.sa_handler = func;
   sigemptyset(&act.sa_mask);
   act.sa_flags = 0;
   if(signo != SIGALRM) act.sa_flags |= SA_RESTART;
   if(sigaction(signo, &act, &oact)<0) return(SIG_ERR);
   return(oact.sa_handler);
}

int main(int argc, char ** argv){
   int connfd=0, i=0, cuid=0;
   int abortfd=0;
   struct sockaddr_in  addr;
   size_t socksize = sizeof(struct sockaddr_in);
   pid_t pid;
   int stat=0;
   FILE * fp;
   struct passwd *pws;
   struct proxycontext * p;
   char * responsemsg;
   int virusdirlen=0;
   char chownit[100];
#define CHOWNCMD "/bin/chown"
   int len=0;
   int ret=0;
   FILE * chowncmd;
   unsigned long kbfree;
   struct statvfs fs;

   w_memory_init();                  // We need to initialize our memory allocation routines

   parseoptions(argc, argv);

   do_log(LOG_NOTICE, PROGNAME " Version " VERSION);
   do_log(LOG_NOTICE, "Selected scannertype: %s (%s)",
   config->scanner->name,config->scanner->descr);

   if((sockfd=socket(PF_INET,SOCK_STREAM,IPPROTO_TCP))<0) do_log(LOG_EMERG, "ERR: Can't open socket!");
   i = 1;
   setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &i, sizeof(i));
   config->addr.sin_family = AF_INET;

   if (bind(sockfd, (struct sockaddr *) &config->addr, sizeof(config->addr))){
      do_log(LOG_EMERG, "ERR: Can't bind to socket %s:%i",inet_ntoa(config->addr.sin_addr), ntohs(config->addr.sin_port));
   }
   if (listen(sockfd, 5)) do_log(LOG_EMERG, "ERR: Can't listen on socket");
   do_log(LOG_NOTICE, "Listen now on %s:%i", inet_ntoa(config->addr.sin_addr), ntohs(config->addr.sin_port));
   if (!config->debug){
      /* daemonize */
      if ((pid = fork())<0) return(-1);
      else if(pid != 0) exit(0);
      setsid();
      if(chdir("/")) do_log(LOG_CRIT,"ERR: chdir");
      umask(0);
   }
   if ((fp=fopen(config->pidfile, "w+"))!=NULL){
      fprintf(fp, "%i\n", getpid());
      fclose(fp);
   }else do_log(LOG_CRIT, "ERR: Can't write PID to %s", PID_FILE);
   len=strlen(CHOWNCMD)+1+strlen(config->runasuser)+1+strlen(config->runasuser)+1+strlen(config->pidfile)+1;
   snprintf(chownit, len, "%s %s:%s %s", CHOWNCMD, config->runasuser, config->runasuser, config->pidfile);
   if ((chowncmd=popen(chownit, "r"))==NULL){
      do_log(LOG_ALERT, "ERR: Can't '%s' !!!", chowncmd);
      return SCANNER_RET_ERR;
   }
   ret=pclose(chowncmd);
   cuid=getuid();
   if (cuid==0){
      do_log(LOG_NOTICE, "Changing uid (we are root)");
      pws = getpwnam(config->runasuser);
      if (pws == NULL) do_log(LOG_EMERG,"ERR: Unknown User '%s'",config->runasuser);
      if (setgid(pws->pw_gid) == -1) do_log(LOG_EMERG, "Can't change to group of user %s (%i.%i)", config->runasuser, pws->pw_uid, pws->pw_gid);
      if (setuid(pws->pw_uid) == -1) do_log(LOG_EMERG, "Can't change to user %s (%i)", config->runasuser, pws->pw_uid);
   }
   cuid=getuid();
   pws = getpwuid(cuid);
   do_log(LOG_NOTICE, "Running as user: %s",pws->pw_name);
   if (p3signal(SIGCHLD, do_sigchld)<0) do_log(LOG_EMERG, "ERR: Could not set signal handler SIGCHLD");
   if (p3signal(SIGTERM, do_sigterm_main)<0) do_log(LOG_EMERG, "ERR: Could not set signal handler SIGTERM main");
   if (p3signal(SIGINT, do_sigterm_main)<0) do_log(LOG_EMERG, "ERR: Could not set signal handler SIGINT main");
   if (config->scanner->init1){
      if (config->scanner->init1()!=0){
         do_log(LOG_CRIT, "ERR: Scanner init failed! Check config and restart " PROGNAME);
         config->scannerenabled = 0;
      }else config->scannerenabled = 1;
   }else config->scannerenabled = 1;
   if (config->quiet){
      config->quiet=0;
      do_log(LOG_NOTICE, "%s %s started.", PROGNAME, VERSION);
      config->quiet=1;
   }
   if (config->debug){
      do_log(LOG_DEBUG,"p3scan.conf:");
      do_log(LOG_DEBUG,"pidfile: %s",config->pidfile);
      do_log(LOG_DEBUG,"maxchilds: %i",config->maxchilds);
      if (!ntohs(config->addr.sin_addr.s_addr)){
         do_log(LOG_DEBUG,"ip: Any");
      } else do_log(LOG_DEBUG,"ip: %i",ntohs(config->addr.sin_addr.s_addr));
      do_log(LOG_DEBUG,"port: %d",htons(config->addr.sin_port));
      if (htonl(INADDR_ANY) == (config->targetaddr.sin_addr.s_addr)) do_log(LOG_DEBUG,"targetip/port disabled");
      else {
         do_log(LOG_DEBUG,"targetip: %i",ntohs(config->targetaddr.sin_addr.s_addr));
         do_log(LOG_DEBUG,"targetport: %d",htons(config->targetaddr.sin_port));
      }
      do_log(LOG_DEBUG,"user: %s",config->runasuser);
      do_log(LOG_DEBUG,"notifydir: %s",config->notifydir);
      do_log(LOG_DEBUG,"virusdir: %s",config->virusdir);
      if(config->delit) do_log(LOG_DEBUG,"justdelete: enabled");
      else do_log(LOG_DEBUG,"justdelete: disabled");
      do_log(LOG_DEBUG,"bytesfree: %lu",config->freespace);
#ifdef DEMIME
      if(config->demime) do_log(LOG_DEBUG,"demime: enabled");
      else do_log(LOG_DEBUG,"demime: disabled");
#else
      do_log(LOG_DEBUG,"DEMIME - Not Available!");
#endif
      if(strlen(NONULL(config->virusscanner))) do_log(LOG_DEBUG,"scanner: %s",config->virusscanner);
      if(strlen(NONULL(config->virusregexp))) do_log(LOG_DEBUG,"virusregexp: %s",config->virusregexp);
      if(config->broken) do_log(LOG_DEBUG,"broken: enabled");
      else do_log(LOG_DEBUG,"broken: disabled");
      if(config->checkspam) do_log(LOG_DEBUG,"checkspam: enabled");
      else do_log(LOG_DEBUG, "checkspam: disabled");
      if(strlen(NONULL(config->spamcheck))) do_log(LOG_DEBUG,"spamcheck: %s",config->spamcheck);
      if(strlen(NONULL(config->renattach))) do_log(LOG_DEBUG,"renattach: %s",config->renattach);
      if(strlen(NONULL(config->overwrite))) do_log(LOG_DEBUG,"overwrite: %s",config->overwrite);
      do_log(LOG_DEBUG,"debug: enabled");
      if(config->quiet) do_log(LOG_DEBUG,"quiet: enabled");
      else do_log(LOG_DEBUG,"quiet: disabled");
      if(strlen(NONULL(config->virustemplate))) do_log(LOG_DEBUG,"template: %s",config->virustemplate);
      if(strlen(NONULL(config->subject))) do_log(LOG_DEBUG,"subject: %s",config->subject);
      if(strlen(NONULL(config->notify))) do_log(LOG_DEBUG,"notify: %s",config->notify);
      if(strlen(NONULL(config->extra))) do_log(LOG_DEBUG,"extra: %s",config->extra);
      do_log(LOG_DEBUG,"emailport: %i",config->smtpport);
      if(strlen(NONULL(config->smtprset))) do_log(LOG_DEBUG,"smtprset: %s",config->smtprset);
      if(config->smtpsize) do_log(LOG_DEBUG,"smtpsize: %i",config->smtpsize);
      else do_log(LOG_DEBUG,"smtpsize: not checking.");
      do_log(LOG_DEBUG,"sslport: %i",config->sslport);
      if(strlen(NONULL(config->mail))) do_log(LOG_DEBUG,"mail: %s",config->mail);
      do_log(LOG_DEBUG,"timeout: %i",config->timeout);
      if(strlen(NONULL(config->footer))) do_log(LOG_DEBUG,"footer: %s",config->footer);
      if(config->altemail) do_log(LOG_DEBUG,"altvnmsg: enabled");
      else do_log(LOG_DEBUG,"altvnmsg: disabled");
      if(config->useurl) do_log(LOG_DEBUG,"useurl: enabled");
      else do_log(LOG_DEBUG,"useurl: disabled");
      if(strlen(NONULL(config->emergcon))) do_log(LOG_DEBUG,"emergcon: %s",config->emergcon);
      if (config->enabletop) do_log(LOG_DEBUG,"TOP processing enabled");
      else do_log(LOG_DEBUG,"TOP processing disabled");
      do_log(LOG_DEBUG,"PIPELINING processing disabled");
      do_log(LOG_DEBUG,"STLS processing disabled");
   }
   numprocs=0;
   do_log(LOG_DEBUG, "Waiting for connections.....");
   while ((connfd = accept(sockfd, (struct sockaddr *)&addr,&socksize)) >= 0){
      if ((abortfd=open(ABORTFILE,O_RDONLY))>=0){
         do_log(LOG_DEBUG,"Aloha No Ka ko");
         close(abortfd);
         unlink(ABORTFILE);
         do_sigterm_main(-1);
         exit(1);
      }
      if ((pid=fork())>0){
         /* parent */
         numprocs++;
         do_log(LOG_DEBUG, "Forked, pid=%i, numprocs=%i", pid, numprocs);
         close (connfd);
         /* wir brauchen die nicht, der childprocess kümmert sich drum
            we don't need "them" (connfd?), child process takes care of that */
         if (numprocs>=config->maxchilds){
            do_log(LOG_WARNING, "MAX_CHILDS (%i) reached!", config->maxchilds);
            while (1){
               pid=waitpid(-1, &stat, 0); /* blocking */
               if (do_sigchld_check(pid, stat)) break;
            }
         }
      }else{
         /* child */
         config->child=1;
         if ( statvfs( config->virusdir, &fs ) == SCANNER_RET_ERR){
            config->emergency="Unable to get available space!";
            do_log(LOG_EMERG, "ERR: Unable to get available space!");
            return SCANNER_RET_CRIT; // Should never reach here, but keep it clean. :)
         }
         if (fs.f_bsize==1024) kbfree=fs.f_bavail;
         else kbfree=fs.f_bsize * (fs.f_bavail / 1024) + fs.f_bavail%1024 * fs.f_bsize / 1024;
         if (config->freespace != 0 && kbfree < config->freespace){
            config->emergency=make_message("Not enough space! Available space: %lu", kbfree);
            do_log(LOG_EMERG, "ERR: Not enough space! Available space: %lu", kbfree);
            do_sigterm_proxy(1);
            exit(0);
         }

         virusdirlen=strlen(config->virusdirbase)+20;
         config->virusdir=w_malloc(virusdirlen);
         snprintf(config->virusdir, virusdirlen, "%s/children/%d/", config->virusdirbase,getpid());
         do_log(LOG_DEBUG, "setting the virusdir to %s", config->virusdir);

         if(clean_child_directory(getpid())){
            config->emergency="Error calling clean child directory!";
            do_log(LOG_EMERG, "ERR: Error calling clean child directory!");
         }
         if((mkdir (config->virusdir, S_IRWXU | S_IRGRP | S_IXGRP)<0)){
            config->emergency=make_message("Could not create virusdir %s", config->virusdir);
            do_log(LOG_EMERG,"ERR: Could not create virusdir %s",config->virusdir);
         }
         if (p3signal(SIGCHLD, NULL)<0) {
            config->emergency="Could not set signal handler SIGCHLD NULL";
            do_log(LOG_EMERG, "ERR: Could not set signal handler SIGCHLD NULL"); /* unset signal handler for child */
         }
         if (p3signal(SIGPIPE, SIG_IGN)<0) {
            config->emergency="Could not set signal handler SIGPIPE";
            do_log(LOG_EMERG, "ERR: Could not set signal handler SIGPIPE"); /* don't die on SIGPIPE */
         }
         do_log(LOG_DEBUG, "Initialize Context");
         p=context_init();
         p->client_fd=connfd;
         p->client_addr=addr;
         global_p=p;
         if (p3signal(SIGTERM, do_sigterm_proxy)<0) {
            config->emergency="Could not set signal handler SIGTERM child";
            do_log(LOG_EMERG, "ERR: Could not set signal handler SIGTERM child");
         }
         if (p3signal(SIGINT,  do_sigterm_proxy)<0) {
            config->emergency="Could not set signal handler SIGINT child";
            do_log(LOG_EMERG, "ERR: Could not set signal handler SIGINT child");
         }
         do_log(LOG_DEBUG, "starting proxy");
         if (proxy(p)){
            /* error, but a message has already be sent */
            responsemsg=strdup("Critical abort");
         }else responsemsg=strdup("Clean Exit");

         if (config->scannerenabled){
            do_log(LOG_NOTICE, "Session done (%s). Mails: %i Bytes: %lu",
            responsemsg, p->mailcount, p->bytecount);
         }else{
            do_log(LOG_NOTICE, "Session done (%s). Mails: %i",
            responsemsg, p->mailcount);
         }
         /* responsemsg created w/malloc through strdup */
         free(responsemsg);
         do_sigterm_proxy(-1);
         exit(0);
      }
   }
   do_log(LOG_NOTICE, "ERR: Accept error - Should not have reached here!");
   do_sigterm_main(-1);
   return 0;
}
