  4ba380:	4c 8d 64 24 f8       	lea    r12,[rsp-0x8]
  4ba385:	4d 3b 66 10          	cmp    r12,QWORD PTR [r14+0x10]
  4ba389:	0f 86 41 03 00 00    	jbe    0x4ba6d0
  4ba38f:	55                   	push   rbp
  4ba390:	48 89 e5             	mov    rbp,rsp
  4ba393:	48 83 c4 80          	add    rsp,0xffffffffffffff80
  4ba397:	48 8b 53 08          	mov    rdx,QWORD PTR [rbx+0x8]
  4ba39b:	48 0b 53 10          	or     rdx,QWORD PTR [rbx+0x10]
  4ba39f:	48 0b 53 18          	or     rdx,QWORD PTR [rbx+0x18]
  4ba3a3:	48 85 d2             	test   rdx,rdx
  4ba3a6:	75 42                	jne    0x4ba3ea
  4ba3a8:	48 8b 13             	mov    rdx,QWORD PTR [rbx]
  4ba3ab:	90                   	nop
  4ba3ac:	48 0f bd ca          	bsr    rcx,rdx
  4ba3b0:	48 c7 c3 ff ff ff ff 	mov    rbx,0xffffffffffffffff
  4ba3b7:	48 0f 44 cb          	cmove  rcx,rbx
  4ba3bb:	48 83 c1 02          	add    rcx,0x2
  4ba3bf:	48 d1 e9             	shr    rcx,1
  4ba3c2:	bb 01 00 00 00       	mov    ebx,0x1
  4ba3c7:	48 d3 e3             	shl    rbx,cl
  4ba3ca:	48 83 fa 02          	cmp    rdx,0x2
  4ba3ce:	0f 83 be 02 00 00    	jae    0x4ba692
  4ba3d4:	44 0f 11 78 10       	movups XMMWORD PTR [rax+0x10],xmm15
  4ba3d9:	48 c7 40 08 00 00 00 	mov    QWORD PTR [rax+0x8],0x0
  4ba3e0:	00 
  4ba3e1:	48 89 10             	mov    QWORD PTR [rax],rdx
  4ba3e4:	48 83 ec 80          	sub    rsp,0xffffffffffffff80
  4ba3e8:	5d                   	pop    rbp
  4ba3e9:	c3                   	ret
  4ba3ea:	48 89 84 24 90 00 00 	mov    QWORD PTR [rsp+0x90],rax
  4ba3f1:	00 
  4ba3f2:	48 89 9c 24 98 00 00 	mov    QWORD PTR [rsp+0x98],rbx
  4ba3f9:	00 
  4ba3fa:	90                   	nop
  4ba3fb:	48 8d 54 24 60       	lea    rdx,[rsp+0x60]
  4ba400:	44 0f 11 3a          	movups XMMWORD PTR [rdx],xmm15
  4ba404:	44 0f 11 7a 10       	movups XMMWORD PTR [rdx+0x10],xmm15
  4ba409:	90                   	nop
  4ba40a:	48 c7 44 24 60 01 00 	mov    QWORD PTR [rsp+0x60],0x1
  4ba411:	00 00 
  4ba413:	90                   	nop
  4ba414:	48 8d 74 24 40       	lea    rsi,[rsp+0x40]
  4ba419:	44 0f 11 3e          	movups XMMWORD PTR [rsi],xmm15
  4ba41d:	44 0f 11 7e 10       	movups XMMWORD PTR [rsi+0x10],xmm15
  4ba422:	48 8b 73 18          	mov    rsi,QWORD PTR [rbx+0x18]
  4ba426:	48 85 f6             	test   rsi,rsi
  4ba429:	74 18                	je     0x4ba443
  4ba42b:	48 0f bd f6          	bsr    rsi,rsi
  4ba42f:	48 c7 c7 ff ff ff ff 	mov    rdi,0xffffffffffffffff
  4ba436:	48 0f 44 f7          	cmove  rsi,rdi
  4ba43a:	48 81 c6 c1 00 00 00 	add    rsi,0xc1
  4ba441:	eb 54                	jmp    0x4ba497
  4ba443:	48 8b 73 10          	mov    rsi,QWORD PTR [rbx+0x10]
  4ba447:	48 85 f6             	test   rsi,rsi
  4ba44a:	74 18                	je     0x4ba464
  4ba44c:	48 0f bd f6          	bsr    rsi,rsi
  4ba450:	48 c7 c7 ff ff ff ff 	mov    rdi,0xffffffffffffffff
  4ba457:	48 0f 44 f7          	cmove  rsi,rdi
  4ba45b:	48 81 c6 81 00 00 00 	add    rsi,0x81
  4ba462:	eb 33                	jmp    0x4ba497
  4ba464:	48 8b 73 08          	mov    rsi,QWORD PTR [rbx+0x8]
  4ba468:	48 85 f6             	test   rsi,rsi
  4ba46b:	74 15                	je     0x4ba482
  4ba46d:	48 0f bd f6          	bsr    rsi,rsi
  4ba471:	48 c7 c7 ff ff ff ff 	mov    rdi,0xffffffffffffffff
  4ba478:	48 0f 44 f7          	cmove  rsi,rdi
  4ba47c:	48 83 c6 41          	add    rsi,0x41
  4ba480:	eb 15                	jmp    0x4ba497
  4ba482:	48 8b 3b             	mov    rdi,QWORD PTR [rbx]
  4ba485:	48 0f bd f7          	bsr    rsi,rdi
  4ba489:	48 c7 c7 ff ff ff ff 	mov    rdi,0xffffffffffffffff
  4ba490:	48 0f 44 f7          	cmove  rsi,rdi
  4ba494:	48 ff c6             	inc    rsi
  4ba497:	48 8d 4e 01          	lea    rcx,[rsi+0x1]
  4ba49b:	48 d1 e9             	shr    rcx,1
  4ba49e:	48 89 d0             	mov    rax,rdx
  4ba4a1:	48 89 c3             	mov    rbx,rax
  4ba4a4:	e8 57 f3 ff ff       	call   0x4b9800
  4ba4a9:	48 8b 9c 24 98 00 00 	mov    rbx,QWORD PTR [rsp+0x98]
  4ba4b0:	00 
  4ba4b1:	48 8b 53 18          	mov    rdx,QWORD PTR [rbx+0x18]
  4ba4b5:	48 85 d2             	test   rdx,rdx
  4ba4b8:	74 18                	je     0x4ba4d2
  4ba4ba:	48 0f bd d2          	bsr    rdx,rdx
  4ba4be:	48 c7 c6 ff ff ff ff 	mov    rsi,0xffffffffffffffff
  4ba4c5:	48 0f 44 d6          	cmove  rdx,rsi
  4ba4c9:	48 81 c2 c1 00 00 00 	add    rdx,0xc1
  4ba4d0:	eb 54                	jmp    0x4ba526
  4ba4d2:	48 8b 53 10          	mov    rdx,QWORD PTR [rbx+0x10]
  4ba4d6:	48 85 d2             	test   rdx,rdx
  4ba4d9:	74 18                	je     0x4ba4f3
  4ba4db:	48 0f bd d2          	bsr    rdx,rdx
  4ba4df:	48 c7 c6 ff ff ff ff 	mov    rsi,0xffffffffffffffff
  4ba4e6:	48 0f 44 d6          	cmove  rdx,rsi
  4ba4ea:	48 81 c2 81 00 00 00 	add    rdx,0x81
  4ba4f1:	eb 33                	jmp    0x4ba526
  4ba4f3:	48 8b 53 08          	mov    rdx,QWORD PTR [rbx+0x8]
  4ba4f7:	48 85 d2             	test   rdx,rdx
  4ba4fa:	74 15                	je     0x4ba511
  4ba4fc:	48 0f bd d2          	bsr    rdx,rdx
  4ba500:	48 c7 c6 ff ff ff ff 	mov    rsi,0xffffffffffffffff
  4ba507:	48 0f 44 d6          	cmove  rdx,rsi
  4ba50b:	48 83 c2 41          	add    rdx,0x41
  4ba50f:	eb 15                	jmp    0x4ba526
  4ba511:	48 8b 33             	mov    rsi,QWORD PTR [rbx]
  4ba514:	48 0f bd d6          	bsr    rdx,rsi
  4ba518:	48 c7 c6 ff ff ff ff 	mov    rsi,0xffffffffffffffff
  4ba51f:	48 0f 44 d6          	cmove  rdx,rsi
  4ba523:	48 ff c2             	inc    rdx
  4ba526:	48 8d 4a 01          	lea    rcx,[rdx+0x1]
  4ba52a:	48 d1 e9             	shr    rcx,1
  4ba52d:	48 8d 44 24 40       	lea    rax,[rsp+0x40]
  4ba532:	e8 89 f4 ff ff       	call   0x4b99c0
  4ba537:	eb 4c                	jmp    0x4ba585
  4ba539:	90                   	nop
  4ba53a:	48 89 74 24 60       	mov    QWORD PTR [rsp+0x60],rsi
  4ba53f:	4c 89 7c 24 68       	mov    QWORD PTR [rsp+0x68],r15
  4ba544:	48 89 5c 24 70       	mov    QWORD PTR [rsp+0x70],rbx
  4ba549:	48 89 4c 24 78       	mov    QWORD PTR [rsp+0x78],rcx
  4ba54e:	90                   	nop
  4ba54f:	44 0f 11 7c 24 50    	movups XMMWORD PTR [rsp+0x50],xmm15
  4ba555:	44 0f 11 7c 24 40    	movups XMMWORD PTR [rsp+0x40],xmm15
  4ba55b:	48 8d 44 24 40       	lea    rax,[rsp+0x40]
  4ba560:	bb 04 00 00 00       	mov    ebx,0x4
  4ba565:	48 89 d9             	mov    rcx,rbx
  4ba568:	48 8b bc 24 98 00 00 	mov    rdi,QWORD PTR [rsp+0x98]
  4ba56f:	00 
  4ba570:	48 89 ce             	mov    rsi,rcx
  4ba573:	49 89 c8             	mov    r8,rcx
  4ba576:	4c 8d 4c 24 60       	lea    r9,[rsp+0x60]
  4ba57b:	45 31 d2             	xor    r10d,r10d
  4ba57e:	66 90                	xchg   ax,ax
  4ba580:	e8 bb d3 ff ff       	call   0x4b7940
  4ba585:	48 8b 54 24 40       	mov    rdx,QWORD PTR [rsp+0x40]
  4ba58a:	4c 8b 5c 24 60       	mov    r11,QWORD PTR [rsp+0x60]
  4ba58f:	90                   	nop
  4ba590:	4d 89 dc             	mov    r12,r11
  4ba593:	49 01 d3             	add    r11,rdx
  4ba596:	4c 89 5c 24 40       	mov    QWORD PTR [rsp+0x40],r11
  4ba59b:	49 d1 eb             	shr    r11,1
  4ba59e:	4c 8b 6c 24 48       	mov    r13,QWORD PTR [rsp+0x48]
  4ba5a3:	4c 8b 7c 24 68       	mov    r15,QWORD PTR [rsp+0x68]
  4ba5a8:	4c 89 e0             	mov    rax,r12
  4ba5ab:	49 01 d4             	add    r12,rdx
  4ba5ae:	4d 89 fc             	mov    r12,r15
  4ba5b1:	4d 11 ef             	adc    r15,r13
  4ba5b4:	4c 89 7c 24 48       	mov    QWORD PTR [rsp+0x48],r15
  4ba5b9:	4c 89 f9             	mov    rcx,r15
  4ba5bc:	49 c1 e7 3f          	shl    r15,0x3f
  4ba5c0:	4d 09 df             	or     r15,r11
  4ba5c3:	48 d1 e9             	shr    rcx,1
  4ba5c6:	4c 8b 5c 24 50       	mov    r11,QWORD PTR [rsp+0x50]
  4ba5cb:	48 8b 5c 24 70       	mov    rbx,QWORD PTR [rsp+0x70]
  4ba5d0:	48 89 c6             	mov    rsi,rax
  4ba5d3:	48 01 d0             	add    rax,rdx
  4ba5d6:	4c 89 e0             	mov    rax,r12
  4ba5d9:	4d 11 ec             	adc    r12,r13
  4ba5dc:	49 89 dc             	mov    r12,rbx
  4ba5df:	4c 11 db             	adc    rbx,r11
  4ba5e2:	48 89 5c 24 50       	mov    QWORD PTR [rsp+0x50],rbx
  4ba5e7:	48 89 df             	mov    rdi,rbx
  4ba5ea:	48 c1 e3 3f          	shl    rbx,0x3f
  4ba5ee:	48 09 cb             	or     rbx,rcx
  4ba5f1:	48 d1 ef             	shr    rdi,1
  4ba5f4:	48 8b 4c 24 58       	mov    rcx,QWORD PTR [rsp+0x58]
  4ba5f9:	4c 8b 44 24 78       	mov    r8,QWORD PTR [rsp+0x78]
  4ba5fe:	4c 89 7c 24 40       	mov    QWORD PTR [rsp+0x40],r15
  4ba603:	48 89 5c 24 48       	mov    QWORD PTR [rsp+0x48],rbx
  4ba608:	48 01 d6             	add    rsi,rdx
  4ba60b:	4c 11 e8             	adc    rax,r13
  4ba60e:	4d 11 dc             	adc    r12,r11
  4ba611:	4c 11 c1             	adc    rcx,r8
  4ba614:	48 89 ca             	mov    rdx,rcx
  4ba617:	48 c1 e1 3f          	shl    rcx,0x3f
  4ba61b:	48 09 f9             	or     rcx,rdi
  4ba61e:	48 89 4c 24 50       	mov    QWORD PTR [rsp+0x50],rcx
  4ba623:	48 d1 ea             	shr    rdx,1
  4ba626:	48 89 54 24 58       	mov    QWORD PTR [rsp+0x58],rdx
  4ba62b:	4c 8b 5c 24 60       	mov    r11,QWORD PTR [rsp+0x60]
  4ba630:	4c 8b 64 24 68       	mov    r12,QWORD PTR [rsp+0x68]
  4ba635:	4c 8b 6c 24 70       	mov    r13,QWORD PTR [rsp+0x70]
  4ba63a:	48 8b 44 24 78       	mov    rax,QWORD PTR [rsp+0x78]
  4ba63f:	4c 89 fe             	mov    rsi,r15
  4ba642:	4d 29 df             	sub    r15,r11
  4ba645:	49 89 df             	mov    r15,rbx
  4ba648:	4c 19 e3             	sbb    rbx,r12
  4ba64b:	48 89 cb             	mov    rbx,rcx
  4ba64e:	4c 19 e9             	sbb    rcx,r13
  4ba651:	48 89 d1             	mov    rcx,rdx
  4ba654:	48 19 c2             	sbb    rdx,rax
  4ba657:	48 19 d2             	sbb    rdx,rdx
  4ba65a:	48 f7 da             	neg    rdx
  4ba65d:	0f 1f 00             	nop    DWORD PTR [rax]
  4ba660:	48 85 d2             	test   rdx,rdx
  4ba663:	0f 85 d0 fe ff ff    	jne    0x4ba539
  4ba669:	48 8b 8c 24 90 00 00 	mov    rcx,QWORD PTR [rsp+0x90]
  4ba670:	00 
  4ba671:	4c 89 19             	mov    QWORD PTR [rcx],r11
  4ba674:	4c 89 61 08          	mov    QWORD PTR [rcx+0x8],r12
  4ba678:	4c 89 69 10          	mov    QWORD PTR [rcx+0x10],r13
  4ba67c:	48 89 41 18          	mov    QWORD PTR [rcx+0x18],rax
  4ba680:	48 89 c8             	mov    rax,rcx
  4ba683:	48 83 ec 80          	sub    rsp,0xffffffffffffff80
  4ba687:	5d                   	pop    rbp
  4ba688:	c3                   	ret
  4ba689:	48 89 c8             	mov    rax,rcx
  4ba68c:	48 89 d3             	mov    rbx,rdx
  4ba68f:	48 89 f2             	mov    rdx,rsi
  4ba692:	48 85 db             	test   rbx,rbx
  4ba695:	74 33                	je     0x4ba6ca
  4ba697:	48 89 c1             	mov    rcx,rax
  4ba69a:	48 89 d0             	mov    rax,rdx
  4ba69d:	48 89 d6             	mov    rsi,rdx
  4ba6a0:	31 d2                	xor    edx,edx
  4ba6a2:	48 f7 f3             	div    rbx
  4ba6a5:	48 8d 14 03          	lea    rdx,[rbx+rax*1]
  4ba6a9:	48 d1 ea             	shr    rdx,1
  4ba6ac:	48 39 d3             	cmp    rbx,rdx
  4ba6af:	77 d8                	ja     0x4ba689
  4ba6b1:	44 0f 11 79 10       	movups XMMWORD PTR [rcx+0x10],xmm15
  4ba6b6:	48 c7 41 08 00 00 00 	mov    QWORD PTR [rcx+0x8],0x0
  4ba6bd:	00 
  4ba6be:	48 89 19             	mov    QWORD PTR [rcx],rbx
  4ba6c1:	48 89 c8             	mov    rax,rcx
  4ba6c4:	48 83 ec 80          	sub    rsp,0xffffffffffffff80
  4ba6c8:	5d                   	pop    rbp
  4ba6c9:	c3                   	ret
  4ba6ca:	e8 11 a1 f8 ff       	call   0x4447e0
  4ba6cf:	90                   	nop
  4ba6d0:	48 89 44 24 08       	mov    QWORD PTR [rsp+0x8],rax
  4ba6d5:	48 89 5c 24 10       	mov    QWORD PTR [rsp+0x10],rbx
  4ba6da:	e8 41 36 fc ff       	call   0x47dd20
  4ba6df:	48 8b 44 24 08       	mov    rax,QWORD PTR [rsp+0x8]
  4ba6e4:	48 8b 5c 24 10       	mov    rbx,QWORD PTR [rsp+0x10]
  4ba6e9:	e9 92 fc ff ff       	jmp    0x4ba380
