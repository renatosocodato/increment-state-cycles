#!/usr/bin/env Rscript
# Exact symbolic examples; mechanics-paper palette, EPJ E vector typography.
args<-grep('^--file=',commandArgs(FALSE),value=TRUE)[1];here<-dirname(normalizePath(sub('^--file=','',args)))
suppressPackageStartupMessages({library(ggplot2);library(cowplot);library(svglite)})
cowplot::set_null_device('agg')
navy<-'#315778'; gold<-'#93640B'; grey<-'#69727A'; blue<-'#6D8DA6'; ink<-'#202B37'; pale<-'#E8EFF5'
th<-function() theme_classic(base_size=10,base_family='Arial')+theme(text=element_text(colour=ink),axis.text=element_text(colour=ink,size=9),axis.title=element_text(size=10),axis.line=element_line(linewidth=.28),axis.ticks=element_line(linewidth=.28),legend.title=element_blank(),legend.text=element_text(size=8.5),legend.position='bottom',legend.key.width=grid::unit(8,'mm'),plot.margin=margin(8,8,8,8),plot.background=element_rect(fill='white',colour=NA))
void<-function() theme_void(base_family='Arial')+theme(plot.margin=margin(10,10,10,10),plot.background=element_rect(fill='white',colour=NA))
tagged<-function(a,b,c,d){g<-ggdraw(plot_grid(a,b,c,d,ncol=2));for(k in 1:4)g<-g+draw_label(c('a','b','c','d')[k],x=c(.008,.508,.008,.508)[k],y=c(.992,.992,.492,.492)[k],hjust=0,vjust=1,fontfamily='Arial',fontface='bold',size=12);g}
export<-function(g,name){ggsave(file.path(here,paste0(name,'.pdf')),g,width=7.1,height=6.4,device=cairo_pdf,bg='white');ggsave(file.path(here,paste0(name,'.svg')),g,width=7.1,height=6.4,device=svglite,bg='white');ggsave(file.path(here,paste0(name,'.eps')),g,width=7.1,height=6.4,device=cairo_ps,onefile=FALSE,bg='white');ggsave(file.path(here,paste0(name,'.png')),g,width=7.1,height=6.4,dpi=300,bg='white')}
states<-c('E','P','R')
matdf<-function(m){d<-expand.grid(i=states,j=states,stringsAsFactors=FALSE);d$p<-as.vector(m);d$i<-factor(d$i,levels=rev(states));d$j<-factor(d$j,levels=states);d}
matplot<-function(m,den){d<-matdf(m);ggplot(d,aes(j,i,fill=p/den))+geom_tile(colour='white',linewidth=.4)+geom_text(aes(label=p),family='Arial',size=3.2,colour=ink)+scale_fill_gradient(low='#F1F4F6',high='#A7C0D2',guide='none')+coord_fixed()+labs(x='Next symbol',y='Current symbol')+th()+theme(axis.line=element_blank(),axis.ticks=element_blank())}
# Figure 1: physical parity and distinct parent counterexamples.
a<-ggplot()+annotate('text',x=.6,y=3.6,label='E',family='Arial',size=5,colour=navy)+annotate('text',x=1.3,y=3.6,label='P',family='Arial',size=5,colour=navy)+annotate('text',x=2.7,y=3.6,label='P',family='Arial',size=5,colour=gold)+annotate('text',x=3.4,y=3.6,label='R',family='Arial',size=5,colour=gold)+annotate('segment',x=.78,xend=1.12,y=3.6,yend=3.6,linewidth=.38,arrow=grid::arrow(length=grid::unit(1.7,'mm')),colour=ink)+annotate('segment',x=1.55,xend=2.4,y=3.6,yend=3.6,linewidth=.38,arrow=grid::arrow(length=grid::unit(1.7,'mm')),colour=ink)+annotate('segment',x=2.88,xend=3.22,y=3.6,yend=3.6,linewidth=.38,arrow=grid::arrow(length=grid::unit(1.7,'mm')),colour=ink)+annotate('text',x=2,y=2.85,label='reverse order and exchange E and R',family='Arial',size=3,colour=ink)+annotate('text',x=2,y=2.15,label='q[1] == J[EE] - J[RR]',parse=TRUE,size=3.8,colour=ink)+annotate('text',x=2,y=1.5,label='q[2] == J[EP] - J[PR]',parse=TRUE,size=3.8,colour=ink)+xlim(0,4)+ylim(1,4)+void()
bmat<-matrix(c(18,153,39,75,652,153,117,75,18),3,byrow=TRUE)
cmat<-matrix(c(4,2,2,2,1,1,2,1,1),3,byrow=TRUE)
# Independently reconstruct the 3-position parent's pair table used in panel b.
parent<-matrix(c(.7,.3,0,.1,.3,.6,0,.2,.8),3,byrow=TRUE); pi0<-c(1,3,9)/13
pair_check<-matrix(0,3,3)
symbol<-function(i,j) if(j>i) 1 else if(j==i) 2 else 3
for(i in 1:3) for(j in 1:3) for(k in 1:3) pair_check[symbol(i,j),symbol(j,k)]<-pair_check[symbol(i,j),symbol(j,k)]+pi0[i]*parent[i,j]*parent[j,k]
stopifnot(max(abs(pair_check-bmat/1300))<1e-12)
stopifnot(max(abs(tcrossprod(c(.5,.25,.25))-cmat/16))<1e-12)
b<-matplot(bmat,1300)
c<-matplot(cmat,16)
m0<-matrix(4,3,3);m1<-matrix(c(5,3,4,3,4,5,4,5,3),3,byrow=TRUE)
stopifnot(all(rowSums(m1)==12),all(colSums(m1)==12),m1[1,1]-m1[3,3]==2,m1[1,2]-m1[2,3]==-2)
d0<-matdf(m0);d0$model<-'J0';d1<-matdf(m1);d1$model<-'J1';dm<-rbind(d0,d1)
d<-ggplot(dm,aes(j,i,fill=p))+geom_tile(colour='white',linewidth=.4)+geom_text(aes(label=p),family='Arial',size=3.1,colour=ink)+facet_wrap(~model,nrow=1)+scale_fill_gradient(low='#F1F4F6',high='#A7C0D2',guide='none')+coord_fixed()+labs(x='Next symbol',y='Current symbol')+th()+theme(strip.background=element_blank(),strip.text=element_text(size=10,colour=ink),axis.line=element_blank(),axis.ticks=element_blank())
export(tagged(a,b,c,d),'Figure_1')
noise<-read.csv(file.path(here,'noise_exact.csv'));pairs<-read.csv(file.path(here,'pairs_eta025.csv'));words<-read.csv(file.path(here,'words_eta025.csv'))
pairs$i<-factor(pairs$i,levels=rev(states));pairs$j<-factor(pairs$j,levels=states)
# Figure 2: exact noisy sequence, adjacent pairs and two temporal scales.
a<-ggplot()+annotate('text',x=1,y=2.7,label='E  P  R  E  R  P',family='Arial',size=4.2,colour=navy)+annotate('text',x=1,y=2,label='uniform phase and independent noise',family='Arial',size=3.1,colour=ink)+annotate('text',x=1,y=1.35,label='paste("replacement probability: ", eta)',parse=TRUE,size=3.5,colour=ink)+xlim(-1,3)+ylim(.7,3.2)+void()
b<-ggplot(pairs,aes(j,i,fill=p))+geom_tile(colour='white',linewidth=.4)+geom_text(aes(label=sprintf('%.3f',p)),family='Arial',size=3.1,colour=ink)+scale_fill_gradient(low='#F1F4F6',high='#A7C0D2',guide='none')+coord_fixed()+labs(x='Next symbol',y='Current symbol')+th()+theme(axis.line=element_blank(),axis.ticks=element_blank())
c<-ggplot(noise,aes(eta))+geom_line(aes(y=pre,colour='PRE',linetype='PRE'),linewidth=.75)+geom_line(aes(y=rep,colour='REP',linetype='REP'),linewidth=.75)+scale_colour_manual(values=c('PRE'=navy,'REP'=gold))+scale_linetype_manual(values=c('PRE'='solid','REP'='dashed'))+guides(linetype='none',colour=guide_legend(override.aes=list(linetype=c('solid','dashed'))))+labs(x=expression('Symbol replacement probability, '*eta),y='Triple probability')+th()
d<-ggplot(noise,aes(eta))+geom_line(aes(y=delta,colour='Consecutive triple',linetype='Consecutive triple'),linewidth=.75)+geom_line(aes(y=lag2,colour='Pair, lag 2',linetype='Pair, lag 2'),linewidth=.75)+scale_colour_manual(values=c('Consecutive triple'=navy,'Pair, lag 2'=gold))+scale_linetype_manual(values=c('Consecutive triple'='solid','Pair, lag 2'='dashed'))+guides(linetype='none',colour=guide_legend(override.aes=list(linetype=c('solid','dashed'))))+labs(x=expression('Symbol replacement probability, '*eta),y='Reversal contrast')+th()+theme(legend.text=element_text(size=8))
export(tagged(a,b,c,d),'Figure_2')
# Figure 3: block KL is finite-window information, not a physical rate.
a<-ggplot(noise,aes(eta))+geom_line(aes(y=D3/3,colour='Three symbols',linetype='Three symbols'),linewidth=.75)+geom_line(aes(y=D2/2,colour='One or two symbols',linetype='One or two symbols'),linewidth=.65)+scale_colour_manual(values=c('Three symbols'=navy,'One or two symbols'=grey))+scale_linetype_manual(values=c('Three symbols'='solid','One or two symbols'='dashed'))+guides(linetype='none',colour=guide_legend(override.aes=list(linetype=c('dashed','solid'))))+labs(x=expression('Symbol replacement probability, '*eta),y='Block KL / symbol (nats)')+th()+theme(legend.text=element_text(size=8))
words<-subset(words,word<reverse & abs(difference)>1e-12);words<-words[order(abs(words$difference),decreasing=TRUE),];words<-head(words,8);words$label<-paste(words$word,words$reverse,sep=' / ');words<-words[order(words$difference),];words$label<-factor(words$label,levels=words$label)
b<-ggplot(words,aes(label,difference))+geom_col(fill=navy,width=.65)+coord_flip()+labs(x='Word / physical reverse',y='Probability difference')+th()+theme(axis.text.y=element_text(size=8.3),axis.ticks.y=element_blank())
c<-ggplot(noise,aes(eta,pre/rep))+geom_line(colour=gold,linewidth=.8)+scale_y_log10()+labs(x=expression('Symbol replacement probability, '*eta),y='P(PRE) / P(REP)')+th()
d<-ggplot()+annotate('text',x=0,y=2.8,label='Adjacent-pair symmetry',family='Arial',size=3.8,colour=ink)+annotate('text',x=0,y=2.1,label='paste(D[1], " = ", D[2], " = 0")',parse=TRUE,size=4,colour=navy)+annotate('text',x=0,y=1.35,label='paste(D[3], " > 0  for  0 < ", eta, " < 1")',parse=TRUE,size=4,colour=gold)+annotate('text',x=0,y=.6,label='finite blocks; no dissipation rate inferred',family='Arial',size=3,colour=ink)+xlim(-3,3)+ylim(.1,3.1)+void()
export(tagged(a,b,c,d),'Figure_3')
