> The original design is retained; its local model-reference path was adapted to this standalone package.

# Recuperação finita da construção física: plano antes da execução

18 de novembro de 2026. A construção e o seu ponto de emparelhamento foram escolhidos após os resultados analíticos anteriores; o estudo abaixo é uma avaliação sintética independente de amostragem finita, não uma previsão biológica prospetiva. Pergunta: com trajectórias finitas, quanto da diferença exata de palavras permanece resolúvel numa comparação em que a lei de pares é idêntica? Uma recuperação baixa é um resultado sobre resolução, não equivalência nem ausência de assimetria.

## Modelos

Usar o rotor contínuo estacionário de seis fases com coordenada binária e o controlo contínuo simétrico de dois estados descritos em `../README.md`; γ=1 e a raiz positiva de r(2)=r(1)² em a∈[0,0,999], de modo que k±=(1±a)/2 por intervalo de amostragem Δt e P=exp(L Δt). Usar como terceiro braço o rotor com k+ e k− trocados: a lei de pares mantém-se, o contraste de triplos muda de sinal, mas os dois sentidos são ambos fora de equilíbrio. O controlo de equilíbrio tem f=(1−r(1))/2 por intervalo e é a referência nula conhecida do modelo. Não é um controlo experimental disponível em geral. Para cada trajetória inicializar na distribuição estacionária uniforme e obter amostras a intervalos constantes, sem ruído de observação adicional.

Definição do estimador: (número de palavras de posições 1101 menos número de palavras 1011)/N, onde N é o número de janelas temporais sobrepostas de quatro posições, equivalentes a PRE e REP da série de incrementos. Uma experiência consiste em 24 trajetórias independentes do mesmo modelo, e estima-se o contraste por média das 24 trajetórias de igual tamanho. São dados sintéticos; não interpretar 24 trajetórias simuladas como 24 animais independentes nem transferir o desempenho aos rastreios de microglia.

## Desenho fixo e controlo

Para N=256, 1024 e 4096 janelas por trajetória, gerar 600 experiências de calibração do controlo, mais 600 experiências independentes para avaliação do controlo, 600 para o rotor e 600 para o rotor com drive invertido. Usar as mesmas trajetórias de cada experiência até os três comprimentos, de modo que os três pontos sejam pareados; conjuntos de calibração e avaliação e os três modelos têm fluxos de números aleatórios separados (`SeedSequence`, raiz 2026111803). Nenhuma trajetória cruzará experiências. O número de experiências de avaliação, não o número de janelas, é a unidade de desempenho Monte Carlo.

Para cada N, fixar no conjunto independente de calibração o quantil 95% `higher` da distribuição de |estimador| do controlo; avaliar excedência estrita no conjunto independente. Características principais: média e intervalo central de repetição de 95% do estimador por experiência, valores exatos esperados, limites independentes e proporções de excedência com intervalos de Wilson para 600 experiências. Taxa do controlo é o falso alerta para este controlo e estes dados simulados, não para toda dinâmica reversível. Os intervalos Wilson tratam o limiar já calibrado como fixo; incerteza da calibração não é incluída. Os três comprimentos, os dois sentidos e as 24 trajetórias são convenções deste estudo, não uma receita universal. Não selecionar resultados por p, corte 0,05 ou percentual arbitrário: descrever a dependência da resolução com N e seus limites.

## Condições e verificação

Verificar estação inicial, P estocástica e distribuição uniforme, pares emparelhados entre rotor e controlo, troca de pares e reversão de sinal sob inversão do drive, valor de conjunto do contraste por produtos de matrizes, controlo reversível. Confirmar por enumeração de exemplos de palavras que 1101 e 1011 implementam PRE e REP, e que o número de janelas é N. Comparar as médias simuladas e as quantidades exatas pela distribuição de experiências sem ajustar parâmetros ou repetir simulações para melhorar resultados. O estudo supõe uma máscara binária, canais de observação ideais e parâmetros conhecidos; não valida a máscara, a calibração, a estacionariedade ou a dissipação de nenhum ensaio.

## Custo e regra editorial

Uma execução CPU1/BLAS1, ≤10 GiB, 3 comprimentos e 4 conjuntos × 600 experiências × 24 trajetórias, no máximo 4.099 amostras de posição por trajetória. Parar ao gravar as tabelas; sem alongar automaticamente N ou acrescentar modelos. Incluir no máximo uma quinta figura apenas se o caso físico e a recuperação ou o limite de resolução oferecerem uma explicação física coerente e diferenciada, com precedentes e limitações explícitos. Um sinal nulo, baixa resolução ou IC que inclua zero não decide sozinho a inclusão. Caso contrário conservar a versão de quatro figuras e os resultados como material de análise.
