#!/usr/bin/env Rscript
args<-grep('^--file=',commandArgs(FALSE),value=TRUE)[1]; here<-dirname(normalizePath(sub('^--file=','',args)))
suppressPackageStartupMessages({library(ggplot2);library(cowplot);library(svglite)})
cowplot::set_null_device('agg')
d<-read.csv(file.path(here,'mixing_curves.csv'));d$kl3<-pmax(d$kl3,0)
navy<-'#315778';gold<-'#93640B';ink<-'#202B37'
th<-function() theme_classic(base_size=10,base_family='Arial')+theme(text=element_text(colour=ink),axis.text=element_text(size=9,colour=ink),axis.line=element_line(linewidth=.28),axis.ticks=element_line(linewidth=.28),legend.title=element_blank(),legend.position='bottom',legend.text=element_text(size=8),legend.key.width=grid::unit(7,'mm'),plot.margin=margin(17,8,8,17))
colors<-scale_colour_manual(values=c('Directed'=navy,'Reversible control'=gold))
# Matching curves are deliberately overlaid with hollow control points.
a<-ggplot()+geom_line(data=subset(d,model=='Directed'),aes(reset,offdiag,colour='Directed'),linewidth=.8)+geom_point(data=subset(d,model=='Reversible control' & round(reset*100)%%10==0),aes(reset,offdiag,colour='Reversible control'),shape=1,size=2,stroke=.7)+colors+labs(x=expression('Phase reset probability, '*rho),y='P(EP), adjacent pair')+th()
makeplot<-function(y,label){ggplot(d,aes(x=reset,y=.data[[y]],colour=model,linetype=model))+geom_line(linewidth=.8)+colors+scale_linetype_manual(values=c('Directed'='solid','Reversible control'='dashed'))+guides(linetype='none',colour=guide_legend(override.aes=list(linetype=c('solid','dashed'))))+labs(x=expression('Phase reset probability, '*rho),y=label)+th()}
b<-makeplot('delta3','P(PRE) - P(REP)')
c<-makeplot('lag2','Lag-two reversal contrast')
dd<-makeplot('kl3',expression('Three-symbol divergence, '*D[3]*' (nats)'))
g<-ggdraw(plot_grid(a,b,c,dd,ncol=2));for(k in 1:4)g<-g+draw_label(c('a','b','c','d')[k],x=c(.008,.508,.008,.508)[k],y=c(.992,.992,.492,.492)[k],hjust=0,vjust=1,fontfamily='Arial',fontface='bold',size=12)
for(ext in c('pdf','svg','eps','png')) {f<-file.path(here,paste0('Figure_mixing.',ext)); if(ext=='pdf')ggsave(f,g,width=7.1,height=6.4,device=cairo_pdf,bg='white') else if(ext=='svg')ggsave(f,g,width=7.1,height=6.4,device=svglite,bg='white') else if(ext=='eps')ggsave(f,g,width=7.1,height=6.4,device=cairo_ps,onefile=FALSE,bg='white') else ggsave(f,g,width=7.1,height=6.4,dpi=300,bg='white')}

