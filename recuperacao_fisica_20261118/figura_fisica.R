#!/usr/bin/env Rscript
options(warn=1)
args<-grep('^--file=',commandArgs(FALSE),value=TRUE)[1]
here<-dirname(normalizePath(sub('^--file=','',args)))
suppressPackageStartupMessages({library(ggplot2);library(cowplot);library(jsonlite)})
cowplot::set_null_device('agg')
d<-read.csv(file.path(here,'resumo_recuperacao.csv'))
meta<-jsonlite::fromJSON(file.path(here,'parametros_e_verificacoes.json'))
navy<-'#315778';gold<-'#AD7404';grey<-'#6D8DA6';ink<-'#202B37'; pale<-'#EAF1F6'
th<-function() theme_classic(base_size=11,base_family='Arial')+theme(text=element_text(colour=ink),axis.text=element_text(size=10,colour=ink),axis.title=element_text(size=10.5),axis.line=element_line(linewidth=.28),axis.ticks=element_line(linewidth=.28),legend.title=element_blank(),legend.position='bottom',legend.text=element_text(size=9),legend.key.width=grid::unit(5,'mm'),plot.margin=margin(15,7,6,14),plot.background=element_rect(fill='white',colour=NA))
# Two-state marker on a six-state cyclic model, plus a reversible two-state comparator.
theta<-pi/2-(0:5)*2*pi/6
ring<-data.frame(i=0:5,x=-0.92+.64*cos(theta),y=.10+.64*sin(theta),level=factor(c(0,1,1,0,1,0),levels=c(0,1)))
edge<-data.frame(x=ring$x,y=ring$y,xend=ring$x[c(2:6,1)],yend=ring$y[c(2:6,1)])
ctrl<-data.frame(x=c(.53,1.33),y=c(.15,.15),level=factor(c(0,1),levels=c(0,1)))
a<-ggplot()+geom_segment(data=edge,aes(x=x,y=y,xend=xend,yend=yend),colour='#87929C',linewidth=.65)+
 geom_point(data=ring,aes(x,y,fill=level),size=7,shape=21,colour=ink,stroke=.35)+
 geom_point(data=ctrl,aes(x,y,fill=level),size=7,shape=21,colour=ink,stroke=.35)+
 geom_curve(aes(x=-1.31,y=.92,xend=-.60,yend=.92),curvature=-.34,arrow=arrow(length=unit(2,'mm')),colour=ink,linewidth=.5)+
 geom_curve(aes(x=-1.31,y=-.72,xend=-.60,yend=-.72),curvature=-.34,arrow=arrow(length=unit(2,'mm')),colour=ink,linewidth=.5)+
 geom_segment(aes(x=.60,y=.23,xend=1.24,yend=.23),arrow=arrow(length=unit(2,'mm')),colour=ink,linewidth=.5)+
 geom_segment(aes(x=1.24,y=.07,xend=.60,yend=.07),arrow=arrow(length=unit(2,'mm')),colour=ink,linewidth=.5)+
 annotate('text',x=-.94,y=1.13,label='Driven rotor',family='Arial',size=3.2,colour=ink)+
 annotate('text',x=.92,y=1.13,label='Equilibrium',family='Arial',size=3.2,colour=ink)+
 annotate('text',x=-1.47,y=.85,label='k+ ',family='Arial',size=2.8,colour=ink)+
 annotate('text',x=-1.47,y=-.70,label='k- ',family='Arial',size=2.8,colour=ink)+
 annotate('text',x=.92,y=-.25,label='equal rates',family='Arial',size=2.7,colour=ink)+
 scale_fill_manual(values=c('0'=navy,'1'=gold),labels=c('x = 0','x = h'),name=NULL)+
 coord_equal(xlim=c(-1.7,1.65),ylim=c(-1.03,1.35),clip='off')+theme_void(base_family='Arial')+
 theme(legend.position='bottom',legend.text=element_text(size=9),legend.key.size=unit(3,'mm'),plot.margin=margin(16,8,5,16))
# Common adjacent increment-pair law (one matrix; equal for both systems).
J<-as.matrix(meta$pair_matrix);ms<-expand.grid(i=1:3,j=1:3);ms$value<-mapply(function(i,j) J[i,j],ms$i,ms$j)
ms$lab<-sprintf('%.3f',ms$value)
b<-ggplot(ms,aes(j,4-i,fill=value))+geom_tile(colour='white',linewidth=.6)+
 geom_text(aes(label=lab),family='Arial',size=3.6,colour=ink)+
 scale_fill_gradient(low='#C9DEED',high='#F0CA65',guide='none')+
 scale_x_continuous(breaks=1:3,labels=c('E','P','R'),expand=c(0,0))+
 scale_y_continuous(breaks=1:3,labels=c('R','P','E'),expand=c(0,0))+
 coord_equal()+labs(x='Next increment',y='Current increment',subtitle='Common pair distribution')+th()+
 theme(axis.line=element_blank(),axis.ticks=element_blank(),plot.subtitle=element_text(size=9.5,colour=ink))
d$model<-factor(d$model,levels=c('test_driven','test_control','test_reversed_drive'),labels=c('Driven','Equilibrium','Reversed'))
d$N<-factor(d$windows_per_trajectory,levels=c(256,1024,4096))
colors<-scale_colour_manual(values=c('Driven'=navy,'Equilibrium'=gold,'Reversed'=grey))
shapes<-scale_shape_manual(values=c('Driven'=16,'Equilibrium'=15,'Reversed'=17))
linetypes<-scale_linetype_manual(values=c('Driven'='solid','Equilibrium'='solid','Reversed'='dashed'))
pos<-position_dodge(width=.20)
c<-ggplot(d,aes(N,mean,colour=model,shape=model,linetype=model,group=model))+
 geom_hline(yintercept=0,colour='#AAB2B8',linewidth=.3)+geom_line(position=pos,linewidth=.5)+
 geom_errorbar(aes(ymin=repeat_lo,ymax=repeat_hi),position=pos,width=.12,linewidth=.4)+
 geom_point(position=pos,size=1.7)+colors+shapes+linetypes+
 labs(x='Windows per trajectory',y=expression(hat(Delta)[3]),subtitle='Mean and 95% repetition interval')+th()+theme(legend.position='none',plot.subtitle=element_text(size=9.5,colour=ink))
e<-ggplot(d,aes(N,exceedance_fraction,colour=model,shape=model,linetype=model,group=model))+
 geom_hline(yintercept=.05,colour='#AAB2B8',linetype='dotted',linewidth=.35)+
 geom_line(position=pos,linewidth=.55)+geom_errorbar(aes(ymin=wilson_low,ymax=wilson_high),position=pos,width=.12,linewidth=.35)+
 geom_point(position=pos,size=1.7)+scale_y_continuous(limits=c(0,1),breaks=c(0,.5,1),expand=expansion(mult=c(.02,.04)))+
 colors+shapes+linetypes+labs(x='Windows per trajectory',y='Exceedance fraction',subtitle='Independent control-calibrated cutoff')+th()+
 theme(plot.subtitle=element_text(size=9.5,colour=ink),legend.box='horizontal',legend.spacing.x=unit(2,'mm'))+
 guides(colour=guide_legend(nrow=1),shape=guide_legend(nrow=1),linetype=guide_legend(nrow=1))
g<-ggdraw(plot_grid(a,b,c,e,ncol=2,align='hv'))
for(k in 1:4)g<-g+draw_label(c('a','b','c','d')[k],x=c(.008,.508,.008,.508)[k],y=c(.992,.992,.492,.492)[k],hjust=0,vjust=1,fontfamily='Arial',fontface='bold',size=12)
ggsave(file.path(here,'Figure_physical.pdf'),g,width=7.1,height=6.8,device=cairo_pdf,bg='white')
ggsave(file.path(here,'Figure_physical.svg'),g,width=7.1,height=6.8,device=grDevices::svg,bg='white')
ggsave(file.path(here,'Figure_physical.png'),g,width=7.1,height=6.8,dpi=250,device=ragg::agg_png,bg='white')
