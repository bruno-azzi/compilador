import java.io.UnsupportedEncodingException;
import java.util.HashMap;

import javax.swing.filechooser.FileFilter;
import java.io.FileNotFoundException;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import javax.swing.JTextArea;
import java.io.IOException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.File;

/**
 * Sintático - Aluno: Bruno Lessa Azzi

Gramatica:

<G> ::= 'START' <VAR_LIST> <METHOD_LIST> 'END'
<VAR_LIST> ::= 'VAR' <VARS> ';'
<VARS> ::= <VAR> , <VARS>
<VARS> ::= <VAR> 
<VAR>  ::= <UNIQUE_IDENTIFIER>
<METHOD_LIST> ::= <METHOD> ; <METHOD_LIST>
<METHOD_LIST> ::= <METHOD>
<METHOD> ::= <METHOD_WHEN>
<METHOD> ::= <METHOD_WHILE>
<METHOD> ::= <METHOD_FOR>
<METHOD> ::= <METHOD_ASSIGN>
<METHOD> ::= <METHOD_LOG>
<METHOD> ::= <METHOD_IN_CASE>
<METHOD_WHEN> ::= 'START_WHEN' '(' <CONDITION> ')' <METHOD_LIST> 'END_WHEN'
<METHOD_WHEN> ::= 'START_WHEN' '(' <CONDITION> ')' <METHOD_LIST> 'WHEN_NOT' <METHOD_LIST> 'END_WHEN'
<METHOD_WHILE> ::= 'START_WHILE' <CONDITION> 'DO' <METHOD_LIST> 'END_WHILE'
<METHOD_FOR> ::= 'START_FOR' <VARIABLE> '>>' <EXP> 'UNTIL' <EXP> 'DO' <METHOD_LIST> 'END_FOR' 
<METHOD_ASSIGN> ::= <VARIABLE> '>>' <EXP>
<VARIABLE>  ::= <ID>
<METHOD_LOG> ::= 'LOG' '(' <EXP> ')'
<METHOD_IN_CASE> ::= 'START_IN_CASE' <EXP> <CASES> 'END_IN_CASE'
<CASES> ::= <CASE> ';' <CASES>
<CASES> ::= <CASE>
<CASE> ::= 'WHEN' <EXP> 'DO' <METHOD_LIST>
<CONDITION> ::= <EXP> '>' <EXP> 
<CONDITION> ::= <EXP> '>=' <EXP> 
<CONDITION> ::= <EXP> '<>' <EXP> 
<CONDITION> ::= <EXP> '<=' <EXP> 
<CONDITION> ::= <EXP> '<' <EXP> 
<CONDITION> ::= <EXP> '==' <EXP>
<EXP> ::= <EXP> + <T>
<EXP> ::= <EXP> - <T>
<EXP> ::= <T>
<T> ::= <T> * <F>
<T> ::= <T> / <F>
<T> ::= <T> % <F>
<T> ::= <F>
<F> ::= -<X>
<F> ::= <X> ** <F>
<F> ::= <X>
<X> ::= '(' <EXP> ')'
<X> ::= [0-9]+('.'[0-9]+)
<X> ::= <VAR>
<UNIQUE_IDENTIFIER> ::= [A-Z]+([A-Z]_[0-9]*)

*/

public class Semantico {

  // Lista de tokens
  static final int T_START             =   1;
  static final int T_END               =   2;
  static final int T_VAR               =   3;
  static final int T_VIRGULA           =   4;
  static final int T_PONTO_VIRGULA     =   5;
  static final int T_START_WHEN        =   6;
  static final int T_WHEN_NOT          =   7;
  static final int T_END_WHEN          =   8;
  static final int T_START_WHILE       =   9;
  static final int T_END_WHILE         =  10;
  static final int T_START_FOR         =  11;
  static final int T_SETA              =  12;
  static final int T_UNTIL             =  13;
  static final int T_END_FOR           =  14;
  static final int T_ABRE_PAR          =  16;
  static final int T_FECHA_PAR         =  17;
  static final int T_LOG               =  18;
  static final int T_MAIOR             =  19;
  static final int T_MENOR             =  20;
  static final int T_MAIOR_IGUAL       =  21;
  static final int T_MENOR_IGUAL       =  22;
  static final int T_IGUAL             =  23;
  static final int T_DIFERENTE         =  24;
  static final int T_MAIS              =  25;
  static final int T_MENOS             =  26;
  static final int T_VEZES             =  27;
  static final int T_DIVIDIDO          =  28;
  static final int T_RESTO             =  29;
  static final int T_ELEVADO           =  30;
  static final int T_NUMERO            =  31;
  static final int T_UNIQUE_IDENTIFIER =  33;
  static final int T_WHEN              =  34;
  static final int T_DO     		   =  36;
  static final int T_START_IN_CASE     =  37;
  static final int T_CASE		       =  38;
  static final int T_END_IN_CASE       =  39;
  static final int T_PONTO             =  40;
	  
  static final int T_END_FONTE         =  90;
  static final int T_ERRO_LEX          =  98;
  static final int T_NULO              =  99;

  static final int FIM_ARQUIVO         = 226;

  static final int E_SEM_ERROS         =   0;
  static final int E_ERRO_LEXICO       =   1;
  static final int E_ERRO_SINTATICO    =   2;
  static final int E_ERRO_SEMANTICO    =   3;

  // Variaveis que surgem no Lexico
  static File arqFonte;
  static BufferedReader rdFonte;
  static File arqDestino;
  static char   lookAhead;
  static int    token;
  static String lexema;
  static int    ponteiro;
  static String linhaFonte;
  static int    linhaAtual;
  static int    colunaAtual;
  static String mensagemDeErro;
  static StringBuffer tokensIdentificados = new StringBuffer();

  // Variaveis adicionadas para o sintatico
  static StringBuffer 	regrasReconhecidas = new StringBuffer();
  static int 			estadoCompilacao;
  
  //Variaveis adicionadas para o semantico
  static String 		    ultimoLexema; // criada para poder usar no codigo
                                         // guardar o lexema anterior
  static StringBuffer       codigoPython = new StringBuffer();
  static int 			    nivelIdentacao = 0; // para saber quantos espaços eu dou
  static String		        exp_0;
  static String		        exp_1;
  static String	    	    exp_2;
  static String	    	    exp_alvo;
  static NodoPilhaSemantica nodo;
  static NodoPilhaSemantica nodo_0;
  static NodoPilhaSemantica nodo_1;
  static NodoPilhaSemantica nodo_2;
  static PilhaSemantica     pilhaSemantica = new PilhaSemantica();
  static HashMap<String,Integer> tabelaSimbolos = new HashMap<String,Integer>();

  public static void main( String s[] ) throws ErroLexicoException
  {
      try {
          abreArquivo();
          abreDestino();
          linhaAtual     = 0;
          colunaAtual    = 0;
          ponteiro       = 0;
          linhaFonte     = "";
          token          = T_NULO;
          mensagemDeErro = "";
          tokensIdentificados.append( "Tokens reconhecidos: \n\n" );
          regrasReconhecidas.append( "\n\nRegras reconhecidas: \n\n" );
          estadoCompilacao 	= E_SEM_ERROS;

          // posiciono no primeiro token
          movelookAhead();
          buscaProximoToken();

          analiseSintatica();

          exibeSaida();

          gravaSaida( arqDestino );

          fechaFonte();

      } catch( FileNotFoundException fnfe ) {
          JOptionPane.showMessageDialog( null, "Arquivo nao existe!", "FileNotFoundException!", JOptionPane.ERROR_MESSAGE );
      } catch( UnsupportedEncodingException uee ) {
          JOptionPane.showMessageDialog( null, "Erro desconhecido", "UnsupportedEncodingException!", JOptionPane.ERROR_MESSAGE );
      } catch( IOException ioe ) {
          JOptionPane.showMessageDialog( null, "Erro de io: " + ioe.getMessage(), "IOException!", JOptionPane.ERROR_MESSAGE );
      } catch( ErroLexicoException ele ) {
          JOptionPane.showMessageDialog( null, ele.getMessage(), "Erro Lexico Exception!", JOptionPane.ERROR_MESSAGE );
      } catch( ErroSintaticoException ese ) {
          JOptionPane.showMessageDialog( null, ese.getMessage(), "Erro Sint�tico Exception!", JOptionPane.ERROR_MESSAGE );
      } catch( ErroSemanticoException esme ) {
          JOptionPane.showMessageDialog( null, esme.getMessage(), "Erro Semantico Exception!", JOptionPane.ERROR_MESSAGE );          
      } finally {
          System.out.println( "Execucao terminada!" );
      }
  }

  static void analiseSintatica() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

      g();

      if ( estadoCompilacao == E_ERRO_LEXICO ) {
          JOptionPane.showMessageDialog( null, mensagemDeErro, "Erro Lexico!", JOptionPane.ERROR_MESSAGE );
      } else if ( estadoCompilacao == E_ERRO_SINTATICO ) {
          JOptionPane.showMessageDialog( null, mensagemDeErro, "Erro Sintatico!", JOptionPane.ERROR_MESSAGE );
      } else if ( estadoCompilacao == E_ERRO_SEMANTICO ) {
          JOptionPane.showMessageDialog( null, mensagemDeErro, "Erro Semantico!", JOptionPane.ERROR_MESSAGE );
      } else {
          JOptionPane.showMessageDialog( null, "Analise Sintatica terminada sem erros", "Analise Sintatica terminada!", JOptionPane.INFORMATION_MESSAGE );
		  acumulaRegraSintaticaReconhecida( "<G>" );
      }
  }
  
  // <G> ::= 'START' <VAR_LIST> <METHOD_LIST> 'END'
  private static void g() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_START ) {
		  buscaProximoToken();
		  regraSemantica( 0 );  
		  varList();
		  methodList();
		  if ( token == T_END ) {
			  buscaProximoToken();
			  regraSemantica( 1 );
			  acumulaRegraSintaticaReconhecida( "<G> ::= 'START' <VAR_LIST> <METHOD_LIST> 'END'" );
		  } else {
			  registraErroSintatico( "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <" + linhaFonte + ">\n('end') esperado, mas encontrei: " + lexema );
		  }
	  } else {
		  registraErroSintatico( "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <" + linhaFonte + ">\n('start') esperado, mas encontrei: " + lexema );
	  }
  }

  // <VAR_LIST> ::= 'VAR' <VARS> ';'
  private static void varList() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_VAR ) {
		  buscaProximoToken();
		  vars();
		  if ( token == T_PONTO_VIRGULA ) {
			  buscaProximoToken();
			  acumulaRegraSintaticaReconhecida( "<VAR_LIST> ::= 'VAR' <VARS> ';'" );
		  } else {
			  registraErroSintatico( "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <" + linhaFonte + ">\n';' esperado, mas encontrei: " + lexema );
		  }
	  } else {
		  registraErroSintatico( "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <" + linhaFonte + ">\n('var') esperado, mas encontrei: " + lexema );
	  }
  }
  
  // <VARS> ::= <VAR> , <VARS> | <VAR> 
  private static void vars() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  var();
	  while ( token == T_VIRGULA ) {
		  buscaProximoToken();
		  var();
	  }
	  acumulaRegraSintaticaReconhecida( "<VARS> ::= <VAR> , <VARS> | <VAR>" );
  }
  
  // <VAR> ::= <UNIQUE_IDENTIFIER> 
  private static void var() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
      uniqueIdentifier();
      regraSemantica( 2 );
	  acumulaRegraSintaticaReconhecida( "<VAR> ::= <UNIQUE_IDENTIFIER>" );
  }
  
 //<VARIABLE> ::= <ID> 
  private static void variable() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  uniqueIdentifier();
      regraSemantica( 4 );
	  acumulaRegraSintaticaReconhecida( "<VARIABLE> ::= <UNIQUE_IDENTIFIER>" );
  }
  
  // <UNIQUE_IDENTIFIER> ::= [A-Z]+([A-Z]_[0-9])*
  private static void uniqueIdentifier() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	if ( token == T_UNIQUE_IDENTIFIER ) {
		buscaProximoToken();
		acumulaRegraSintaticaReconhecida( "<UNIQUE_IDENTIFIER> ::= [A-Z]+([A-Z]_[0-9])*" );
	} else {
		registraErroSintatico( "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <" + linhaFonte + ">\nEsperava um identificador. Encontrei: " + lexema );
	}
  }
   
  // <METHOD_LIST> ::= <METHOD> ; <METHOD_LIST> | <METHOD>
  private static void methodList() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  method();
	  while ( token == T_PONTO_VIRGULA ) {
		  buscaProximoToken();
		  method();
	  } 
	  acumulaRegraSintaticaReconhecida( "<METHOD_LIST> ::= <METHOD> ; <METHOD_LIST> | <METHOD>" );
  }
  
  // <METHOD> ::= <METHOD_WHEN>
  // <METHOD> ::= <METHOD_WHILE>
  // <METHOD> ::= <METHOD_FOR>
  // <METHOD> ::= <METHOD_ASSIGN>
  // <METHOD> ::= <METHOD_LOG>
  // <METHOD> ::= <METHOD_IN_CASE>
  private static void method() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
      switch ( token ) {
      case T_START_WHEN: methodWhen(); break;
      case T_START_WHILE: methodWhile(); break;
      case T_START_FOR: methodFor(); break;
      case T_UNIQUE_IDENTIFIER: methodAssign(); break;
      case T_LOG: methodLog(); break;
      case T_START_IN_CASE: methodCase(); break;
      default:
          registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\nMetodo nao identificado va aprender a programar pois encontrei: " + lexema );
      }
	  acumulaRegraSintaticaReconhecida( "<METHOD> ::= <METHOD_WHEN>|<METHOD_WHILE>|<METHOD_FOR>|<METHOD_ASSIGN>|<METHOD_LOG>" );
  }
  
  // <METHOD_WHEN> ::= 'START_WHEN' <CONDITION> <METHOD_LIST> 'END_WHEN' 
  // <METHOD_WHEN> ::= 'START_WHEN' <CONDITION> <METHOD_LIST> 'WHEN_NOT' <METHOD_LIST> 'END_WHEN' 
  private static void methodWhen() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_START_WHEN) {
		  buscaProximoToken();
		  if ( token == T_ABRE_PAR ) {
			  buscaProximoToken();
			  condition();
			  regraSemantica( 17 );
			  if ( token == T_FECHA_PAR ) {
				  buscaProximoToken();
                  methodList();
                  regraSemantica( 14 );
				  if ( token == T_WHEN_NOT ) {
					  buscaProximoToken();
					  regraSemantica( 18 );
					  methodList();
					  regraSemantica( 16 );
				  }
				  if ( token == T_END_WHEN ) {
					  buscaProximoToken();
					  acumulaRegraSintaticaReconhecida( "<METHOD_WHEN> ::= 'START_WHEN' <CONDITION> <METHOD_LIST> ( 'END_WHEN'|'WHEN_NOT' <METHOD_LIST> 'END_WHEN' )" );
				  } else {
					  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'end_when' esperado mas encontrei: " + lexema );  
				  }
			  } else {
				  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n')' esperado mas encontrei: " + lexema );
			  }
		  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'(' esperado mas encontrei: " + lexema ); 
		  }
	  }
  }
  
  // <METHOD_WHILE> ::= 'START_WHILE' <CONDITION> 'DO' <METHOD_LIST> 'END_WHILE'
  private static void methodWhile() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_START_WHILE ) {
		  buscaProximoToken();
		  condition();
		  regraSemantica( 15 );
		  if ( token == T_DO ) {
			  buscaProximoToken();
			  methodList();
			  regraSemantica( 16 );
			  if ( token == T_END_WHILE ) {
				  buscaProximoToken();
				  acumulaRegraSintaticaReconhecida( "<METHOD_WHILE> ::= 'START_WHILE' <CONDITION> 'DO' <METHOD_LIST> 'END_WHILE'" );
			  } else {
				  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'end_while' esperado mas encontrei: " + lexema );
			  }
		  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'do' esperado mas encontrei: " + lexema ); 
		  }
		  
	  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'start_while' esperado mas encontrei: " + lexema ); 
	  }	  
  }

  // <METHOD_FOR> ::= 'START_FOR' <VARIABLE> '>>' <EXP> 'UNTIL' <EXP> 'DO' <METHOD_LIST> 'END_FOR' 
  private static void methodFor() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_START_FOR ) {
		  buscaProximoToken();
		  variable();
		  if ( token == T_SETA ) {
			  buscaProximoToken();
			  exp();
			  if ( token == T_UNTIL ) {
				  buscaProximoToken();
				  exp();
				  regraSemantica( 30 );
				  if ( token == T_DO ) {
					  buscaProximoToken();
					  methodList();
					  if ( token == T_END_FOR ) {
						  buscaProximoToken();
						  regraSemantica( 16 );
						  acumulaRegraSintaticaReconhecida( "<METHOD_FOR> ::= 'START_FOR' <VARIABLE> '>>' <EXP> 'UNTIL' <EXP> 'DO' <METHOD_LIST> 'END_FOR'" );
					  } else {
						  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'end_for' esperado mas encontrei: " + lexema );
					  }
				  } else {
					  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'do' esperado mas encontrei: " + lexema ); 
				  }
			  } else {
				  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'until' esperado mas encontrei: " + lexema );
			  }
		  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'>>' esperado mas encontrei: " + lexema ); 
		  }
	  } else {
		  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'start_for' esperado mas encontrei: " + lexema );
	  }
  }  
  
  // <METHOD_ASSIGN> ::= <VARIABLE> '>>' <EXP>
  private static void methodAssign() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  variable();
	  if ( token == T_SETA ) {
		  buscaProximoToken();
		  exp();
		  regraSemantica( 3 );
		  acumulaRegraSintaticaReconhecida( "<METHOD_ASSIGN> ::= <VARIABLE> '>>' <EXP>" );
	  } else {
		  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'>>' esperado mas encontrei: " + lexema );		  
	  }
  }

  // <METHOD_LOG> ::= 'LOG' '(' <EXP> ')'
  private static void methodLog() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_LOG ) {
		  buscaProximoToken();
		  if ( token == T_ABRE_PAR ) {
			  buscaProximoToken();
			  exp();
			  if ( token == T_FECHA_PAR ) {
				  buscaProximoToken();
				  regraSemantica( 25 );
				  acumulaRegraSintaticaReconhecida( "<METHOD_LOG> ::= 'LOG' '(' <EXP> ')'" );
			  } else {
				  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n')' esperado mas encontrei: " + lexema );
			  }
		  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'(' esperado mas encontrei: " + lexema ); 
		  }
	  } else {
		  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'log' esperado mas encontrei: " + lexema );
	  }
  }


  // <methodCase> ::= 'START_IN_CASE' <EXP> <CASES> 'END_IN_CASE'
  private static void methodCase() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_START_IN_CASE ) {
		  buscaProximoToken();
		  exp();
		  regraSemantica( 31 );
		  cases();
		  if ( token == T_END_IN_CASE ) {
			  buscaProximoToken();
			  regraSemantica( 34 );
			  acumulaRegraSintaticaReconhecida( "<methodCase> ::= 'START_IN_CASE' <EXP> <CASES> 'END_IN_CASE'" );
		  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'end_case' esperado mas encontrei: " + lexema ); 
		  }
	  } else {
		  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'start_in_case' esperado mas encontrei: " + lexema );
	  }
  }
  
  // <CASES> ::= <CASE> '.' <CASES>
  // <CASES> ::= <CASE>
  private static void cases() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  CASE();
	  regraSemantica( 33 );
	  while ( token == T_PONTO ) {
		  buscaProximoToken();
		  CASE();
		  regraSemantica( 33 );
	  } 
	  acumulaRegraSintaticaReconhecida( "<METHOD_LIST> ::= <METHOD> ; <METHOD_LIST> | <METHOD>" );
  }
  
  // <CASE> ::= 'WHEN' <EXP> 'DO' <METHOD_LIST>
  private static void CASE() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

	  if ( token == T_WHEN ) {
		  buscaProximoToken();
		  exp();
		  regraSemantica( 32 );
		  if ( token == T_DO ) {
			  buscaProximoToken();
			  methodList();
			  acumulaRegraSintaticaReconhecida( "<CASE> ::= 'WHEN' <EXP> 'DO' <METHOD_LIST>" );
		  } else {
			  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'do' esperado mas encontrei: " + lexema ); 
		  }
	  } else {
		  registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'when' esperado mas encontrei: " + lexema );
	  }
	  
  }

  // <CONDITION> ::= <EXP> '>' <EXP> 
  // <CONDITION> ::= <EXP> '>=' <EXP> 
  // <CONDITION> ::= <EXP> '<>' <EXP> 
  // <CONDITION> ::= <EXP> '<=' <EXP> 
  // <CONDITION> ::= <EXP> '<' <EXP> 
  // <CONDITION> ::= <EXP> '==' <EXP>
  private static void condition() throws ErroLexicoException, IOException, ErroSintaticoException, ErroSemanticoException {
	  exp();
	  switch ( token ) {
	  case T_MAIOR: buscaProximoToken(); exp(); regraSemantica( 19 ); break; 
	  case T_MENOR: buscaProximoToken(); exp(); regraSemantica( 20 ); break; 
	  case T_MAIOR_IGUAL: buscaProximoToken(); exp(); regraSemantica( 21 ); break; 
	  case T_MENOR_IGUAL: buscaProximoToken(); exp(); regraSemantica( 22 ); break; 
	  case T_IGUAL: buscaProximoToken(); exp(); regraSemantica( 23 ); break; 
	  case T_DIFERENTE: buscaProximoToken(); exp(); regraSemantica( 24 ); break;
	  default: registraErroSintatico( "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <" + linhaFonte + ">\nEsperava um operador logico. Encontrei: " + lexema );
	  }
	  acumulaRegraSintaticaReconhecida( "<CONDITION> ::= <EXP> ('>'|'>='|'<>'|'<='|'<'|'==') <EXP> " );
  }
  
  // <EXP> ::= <EXP> + <T>
  // <EXP> ::= <EXP> - <T>
  // <EXP> ::= <T>
  private static void exp() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  t();
	  while ( (token == T_MAIS) || (token == T_MENOS) ) {
		  switch( token ) {
	      case T_MAIS: { buscaProximoToken();
		  				 t();
		  				 regraSemantica( 5 );
	      	   }
	           break;
	      case T_MENOS: { buscaProximoToken();
	      				  t();
	      				  regraSemantica( 6 );
	      	   }
	           break;
		  }
	  }
	  acumulaRegraSintaticaReconhecida( "<EXP> ::= <EXP> + <T>|<EXP> - <T>|<T> " );
  }
  
  // <T> ::= <T> * <F>
  // <T> ::= <T> / <F>
  // <T> ::= <T> % <F>
  // <T> ::= <F>
  private static void t() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  f();
	  while ( (token == T_VEZES) || (token == T_DIVIDIDO) || (token == T_RESTO) ) {
		  switch ( token ) {
		  case T_VEZES: { buscaProximoToken();
		  				  f();
		  				  regraSemantica( 7 );
		  				}
		                break;
		  case T_DIVIDIDO: { buscaProximoToken();
			  				 f();
			  				 regraSemantica( 8 );
						   }
		                break;
		  case T_RESTO: { buscaProximoToken();
			 		  	  f();
			 		  	  regraSemantica( 9 );
		  				}
		                break;
		  }
	  }
	  acumulaRegraSintaticaReconhecida( "<T> ::= <T> * <F>|<T> / <F>|<T> % <F>|<F>" );
  }
  
  // <F> ::= -<F>
  // <F> ::= <X> ** <F>
  // <F> ::= <X>     
  private static void f() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  if ( token == T_MENOS ) {
		  buscaProximoToken();
		  f();
	  } else {
		  x();
		  while ( token == T_ELEVADO ) {
			  buscaProximoToken();
	          x();
	          regraSemantica( 10 );
		  }
	  }
	  acumulaRegraSintaticaReconhecida( "<F> ::= -<F>|<X> ** <F>|<X> " );
	  
  }
  
  // <X> ::= '(' <EXP> ')'
  // <X> ::= [0-9]+('.'[0-9]+)
  // <X> ::= <VAR>
  private static void x() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
	  switch ( token ) {
	  case T_UNIQUE_IDENTIFIER: buscaProximoToken(); acumulaRegraSintaticaReconhecida( "<X> ::= <VAR>" ); regraSemantica( 11 ); break;
	  case T_NUMERO: buscaProximoToken(); acumulaRegraSintaticaReconhecida( "<X> ::= [0-9]+('.'[0-9]+)" ); regraSemantica( 12 ); break;
	  case T_ABRE_PAR: {
	       buscaProximoToken(); 
	       exp();
	       if ( token == T_FECHA_PAR ) {
	    	   buscaProximoToken();
	    	   acumulaRegraSintaticaReconhecida( "<X> ::= '(' <EXP> ')'" );
	       } else {
			   registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n')' esperado mas encontrei: " + lexema );
	       }
	       regraSemantica( 13 );
	      } break;
	   default: registraErroSintatico( "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\nFator invalido: encontrei: " + lexema );   
	  }
  }
  
  static void fechaFonte() throws IOException
  {
      rdFonte.close();
  }

  static void movelookAhead() throws IOException
  {
	  
    if ( ( ponteiro + 1 ) > linhaFonte.length() ) {

    	linhaAtual++;
        ponteiro = 0;
        
        
        if ( ( linhaFonte = rdFonte.readLine() ) == null ) {
            lookAhead = FIM_ARQUIVO;
        } else {

        	StringBuffer sbLinhaFonte = new StringBuffer( linhaFonte );
        	sbLinhaFonte.append( '\13' ).append( '\10' );
        	linhaFonte = sbLinhaFonte.toString();
        	
            lookAhead = linhaFonte.charAt( ponteiro );
        }
    } else {
        lookAhead = linhaFonte.charAt( ponteiro );
    }

    // Se comentar esse if, eu terei uma linguagem 
    // que diferencia minusculas de maiusculas
    if ( ( lookAhead >= 'a' ) &&
         ( lookAhead <= 'z' ) ) {
        lookAhead = (char) ( lookAhead - 'a' + 'A' );
    }

    ponteiro++;
    colunaAtual = ponteiro + 1;
  }

  static void buscaProximoToken() throws IOException, ErroLexicoException
  {
	int i, j;
	
	if ( lexema != null ) {
        ultimoLexema = new String( lexema );
    }
        
    StringBuffer sbLexema = new StringBuffer( "" );

    // Salto espaçoes enters e tabs até o inicio do proximo token
  	while ( ( lookAhead == 9 ) ||
	        ( lookAhead == '\n' ) ||
	        ( lookAhead == 8 ) ||
	        ( lookAhead == 11 ) ||
	        ( lookAhead == 12 ) ||
	        ( lookAhead == '\r' ) ||
	        ( lookAhead == 32 ) )
    {
        movelookAhead();
    }

    /*--------------------------------------------------------------*
     * CASE o primeiro caracter seja alfabetico, procuro capturar a *
     * sequencia de caracteres que se segue a ele e classifica-la   *
     *--------------------------------------------------------------*/
    if ( ( lookAhead >= 'A' ) && ( lookAhead <= 'Z' ) ) {   
        sbLexema.append( lookAhead );
        movelookAhead();

        while ( ( ( lookAhead >= 'A' ) && ( lookAhead <= 'Z' ) ) ||
        		( ( lookAhead >= '0' ) && ( lookAhead <= '9' ) ) || ( lookAhead == '_' ) )
        {
            sbLexema.append( lookAhead );
            movelookAhead();
        }

        lexema = sbLexema.toString();  

        /* Classifico o meu token como palavra reservada ou id */
        if ( lexema.equals( "START" ) )
            token = T_START;
        else if ( lexema.equals( "END" ) )
            token = T_END;
        else if ( lexema.equals( "VAR" ) )
            token = T_VAR;
        else if ( lexema.equals( "START_WHEN" ) )
            token = T_START_WHEN;
        else if ( lexema.equals( "WHEN_NOT" ) )
            token = T_WHEN_NOT;
        else if ( lexema.equals( "END_WHEN" ) )
            token = T_END_WHEN;
        else if ( lexema.equals( "START_WHILE" ) )
            token = T_START_WHILE;
        else if ( lexema.equals( "END_WHILE" ) )
            token = T_END_WHILE;
        else if ( lexema.equals( "START_FOR" ) )
            token = T_START_FOR;
        else if ( lexema.equals( "UNTIL" ) )
            token = T_UNTIL;
        else if ( lexema.equals( "END_FOR" ) )
            token = T_END_FOR;
        else if ( lexema.equals( "LOG" ) )
            token = T_LOG;
        else if ( lexema.equals( "START_IN_CASE" ) )
            token = T_START_IN_CASE;
        else if ( lexema.equals( "CASE" ) )
            token = T_CASE;
        else if ( lexema.equals( "DO" ) )
            token = T_DO;
        else if ( lexema.equals( "WHEN" ) )
            token = T_WHEN;
        else if ( lexema.equals( "END_IN_CASE" ) )
            token = T_END_IN_CASE;
        else {
        	token = T_UNIQUE_IDENTIFIER;
        }
    } else if ( ( lookAhead >= '0' ) && ( lookAhead <= '9' ) ) {
        sbLexema.append( lookAhead );
        movelookAhead();
        while ( ( lookAhead >= '0' ) && ( lookAhead <= '9' ) )
        {
            sbLexema.append( lookAhead );
            movelookAhead();
        }
        token = T_NUMERO;    	
    } else if ( lookAhead == '(' ){
        sbLexema.append( lookAhead );
        token = T_ABRE_PAR;    	
        movelookAhead();
    } else if ( lookAhead == ')' ){
        sbLexema.append( lookAhead );
        token = T_FECHA_PAR;    	
        movelookAhead();
    } else if ( lookAhead == ';' ){
        sbLexema.append( lookAhead );
        token = T_PONTO_VIRGULA;    	
        movelookAhead();
    } else if ( lookAhead == ',' ){
        sbLexema.append( lookAhead );
        token = T_VIRGULA;    	
        movelookAhead();
    } else if ( lookAhead == '.' ){
        sbLexema.append( lookAhead );
        token = T_PONTO;    	
        movelookAhead();
    } else if ( lookAhead == '+' ){
        sbLexema.append( lookAhead );
        token = T_MAIS;    	
        movelookAhead();
    } else if ( lookAhead == '-' ){
        sbLexema.append( lookAhead );
        token = T_MENOS;    	
        movelookAhead();
    } else if ( lookAhead == '*' ){
        sbLexema.append( lookAhead );
        movelookAhead();
        if ( lookAhead == '*' ) {
            sbLexema.append( lookAhead );
            movelookAhead();
            token = T_ELEVADO;    	
        } else {
            token = T_VEZES;    	
        }
    } else if ( lookAhead == '/' ){
        sbLexema.append( lookAhead );
        token = T_DIVIDIDO;    	
        movelookAhead();
    } else if ( lookAhead == '=' ){
        sbLexema.append( lookAhead ); 	
        movelookAhead();
        if ( lookAhead == '=' ) {
            sbLexema.append( lookAhead );
            movelookAhead();
            token = T_IGUAL;
        }
    } else if ( lookAhead == '%' ){
        sbLexema.append( lookAhead );
        token = T_RESTO;    	
        movelookAhead();
    } else if ( lookAhead == '<' ){
        sbLexema.append( lookAhead );
        movelookAhead();
        if ( lookAhead == '>' ) {
            sbLexema.append( lookAhead );
            movelookAhead();
            token = T_DIFERENTE;
        } else if ( lookAhead == '=' ) {  
            sbLexema.append( lookAhead );
            movelookAhead();
            token = T_MENOR_IGUAL;
        } else {
            token = T_MENOR;    	
        }
    } else if ( lookAhead == '>' ){
        sbLexema.append( lookAhead );
        movelookAhead();
        if ( lookAhead == '=' ) {
            sbLexema.append( lookAhead );
            movelookAhead();
            token = T_MAIOR_IGUAL;
        } else if ( lookAhead == '>' ) {  
            sbLexema.append( lookAhead );
            movelookAhead();
            token = T_SETA;
        } else {
            token = T_MAIOR;    	
        }        
    } else if ( lookAhead == FIM_ARQUIVO ){
         token = T_END_FONTE;    	
    } else {
    	token = T_ERRO_LEX;
    	sbLexema.append( lookAhead );
    }
        
    lexema = sbLexema.toString();  
    
    mostraToken();
    
    if ( token == T_ERRO_LEX ) {
    	mensagemDeErro = "Erro Léxico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\nToken desconhecido: " + lexema;
    	throw new ErroLexicoException( mensagemDeErro );
    } 
  }
  
  static void mostraToken()
  {

    StringBuffer tokenLexema = new StringBuffer( "" );
    
    switch ( token ) {
    case T_START    : tokenLexema.append( "T_START" ); break;
    case T_END    : tokenLexema.append( "T_END" ); break;
    case T_VAR    : tokenLexema.append( "T_VAR" ); break;
    case T_VIRGULA    : tokenLexema.append( "T_VIRGULA" ); break;
    case T_PONTO_VIRGULA    : tokenLexema.append( "T_PONTO_VIRGULA" ); break;
    case T_START_WHEN    : tokenLexema.append( "T_START_WHEN" ); break;
    case T_WHEN_NOT    : tokenLexema.append( "T_WHEN_NOT" ); break;
    case T_END_WHEN    : tokenLexema.append( "T_END_WHEN" ); break;
    case T_START_WHILE    : tokenLexema.append( "T_START_WHILE" ); break;
    case T_END_WHILE    : tokenLexema.append( "T_END_WHILE" ); break;
    case T_START_FOR            : tokenLexema.append( "T_START_FOR" ); break;
    case T_SETA            : tokenLexema.append( "T_SETA" ); break;
    case T_UNTIL             : tokenLexema.append( "T_UNTIL" ); break;
    case T_END_FOR        : tokenLexema.append( "T_END_FOR" ); break;
    case T_ABRE_PAR        : tokenLexema.append( "T_ABRE_PAR" ); break;
    case T_FECHA_PAR       : tokenLexema.append( "T_FECHA_PAR" ); break;
    case T_LOG             : tokenLexema.append( "T_LOG" ); break;
    case T_MAIOR           : tokenLexema.append( "T_MAIOR" ); break;
    case T_MENOR           : tokenLexema.append( "T_MENOR" ); break;
    case T_MAIOR_IGUAL     : tokenLexema.append( "T_MAIOR_IGUAL" ); break;
    case T_MENOR_IGUAL     : tokenLexema.append( "T_MENOR_IGUAL" ); break;
    case T_IGUAL           : tokenLexema.append( "T_IGUAL" ); break;
    case T_DIFERENTE       : tokenLexema.append( "T_DIFERENTE" ); break;
    case T_MAIS            : tokenLexema.append( "T_MAIS" ); break;
    case T_MENOS           : tokenLexema.append( "T_MENOS" ); break;
    case T_VEZES           : tokenLexema.append( "T_VEZES" ); break;
    case T_DIVIDIDO        : tokenLexema.append( "T_DIVIDIDO" ); break;
    case T_RESTO           : tokenLexema.append( "T_RESTO" ); break;
    case T_ELEVADO         : tokenLexema.append( "T_ELEVADO" ); break;
    case T_NUMERO          : tokenLexema.append( "T_NUMERO" ); break;
    case T_UNIQUE_IDENTIFIER : tokenLexema.append( "T_UNIQUE_IDENTIFIER" ); break;
    case T_END_FONTE       : tokenLexema.append( "T_END_FONTE" ); break;
    case T_ERRO_LEX        : tokenLexema.append( "T_ERRO_LEX" ); break;
    case T_NULO            : tokenLexema.append( "T_NULO" ); break;
    case T_START_IN_CASE    : tokenLexema.append( "T_START_IN_CASE" ); break;
    case T_CASE            : tokenLexema.append( "T_CASE" ); break;
    case T_WHEN           :  tokenLexema.append( "T_WHEN" ); break;
    case T_DO           :  tokenLexema.append( "T_DO" ); break;
    case T_END_IN_CASE        : tokenLexema.append( "T_END_IN_CASE" ); break;
    case T_PONTO           : tokenLexema.append( "T_PONTO" ); break;
    
    default                : tokenLexema.append( "N/A" ); break;
    }
    System.out.println( tokenLexema.toString() + " ( " + lexema + " )" );
    acumulaToken( tokenLexema.toString() + " ( " + lexema + " )" );
    tokenLexema.append( lexema );
  }
  
  private static void abreArquivo() {

		JFileChooser fileChooser = new JFileChooser();
		
		fileChooser.setFileSelectionMode( JFileChooser.FILES_ONLY );

		FiltroSab filtro = new FiltroSab();
	    
		fileChooser.addChoosableFileFilter( filtro );
		int result = fileChooser.showOpenDialog( null );
		
		if( result == JFileChooser.CANCEL_OPTION ) {
			return;
		}
		
		arqFonte = fileChooser.getSelectedFile();
		abreFonte( arqFonte ); 	

	}


	private static boolean abreFonte( File fileName ) {

		if( arqFonte == null || fileName.getName().trim().equals( "" ) ) {
			JOptionPane.showMessageDialog( null, "Nome de Arquivo Invalido", "Nome de Arquivo Invalido", JOptionPane.ERROR_MESSAGE );
			return false;
		} else {
			linhaAtual = 1;
	        try {
				FileReader fr = new FileReader( arqFonte );
				rdFonte = new BufferedReader( fr );
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			} 
			return true;
		}
	}

	private static void abreDestino() {

		JFileChooser fileChooser = new JFileChooser();
			
		fileChooser.setFileSelectionMode( JFileChooser.FILES_ONLY );

		FiltroSab filtro = new FiltroSab();
		    
		fileChooser.addChoosableFileFilter( filtro );
		int result = fileChooser.showSaveDialog( null );
			
		if( result == JFileChooser.CANCEL_OPTION ) {
			return;
		}
			
		arqDestino = fileChooser.getSelectedFile();
	}	
	

	private static boolean gravaSaida( File fileName ) {

		if( arqDestino == null || fileName.getName().trim().equals( "" ) ) {
			JOptionPane.showMessageDialog( null, "Nome de Arquivo Invalido", "Nome de Arquivo Invalido", JOptionPane.ERROR_MESSAGE );
			return false;
		} else {
			FileWriter fw;
			try {
				System.out.println( arqDestino.toString() );
				System.out.println( tokensIdentificados.toString() );
				fw = new FileWriter( arqDestino );
				BufferedWriter bfw = new BufferedWriter( fw ); 
//				bfw.write( tokensIdentificados.toString() );
//				bfw.write( regrasReconhecidas.toString() );
				bfw.write( codigoPython.toString() );
				bfw.close();
				JOptionPane.showMessageDialog( null, "Arquivo Salvo: " + arqDestino, "Salvando Arquivo", JOptionPane.INFORMATION_MESSAGE );
			} catch (IOException e) {
				JOptionPane.showMessageDialog( null, e.getMessage(), "Erro de Entrada/Sa�da", JOptionPane.ERROR_MESSAGE );
			} 
			return true;
		}
	}
	
	public static void exibeTokens() {
		
		JTextArea texto = new JTextArea();
		texto.append( tokensIdentificados.toString() );
		JOptionPane.showMessageDialog(null, texto, "Tokens Identificados (token/lexema)", JOptionPane.INFORMATION_MESSAGE );
	}
	
	
	public static void acumulaRegraSintaticaReconhecida( String regra ) {

		regrasReconhecidas.append( regra );
		regrasReconhecidas.append( "\n" );
		
	}
	
	public static void acumulaToken( String tokenIdentificado ) {

		tokensIdentificados.append( tokenIdentificado );
		tokensIdentificados.append( "\n" );
		
	}
	
    public static void exibeSaida() {

        JTextArea texto = new JTextArea();
        texto.append( tokensIdentificados.toString() );
        JOptionPane.showMessageDialog(null, texto, "Analise Lexica", JOptionPane.INFORMATION_MESSAGE );

        texto.setText( regrasReconhecidas.toString() );
        texto.append( "\n\nStatus da Compilacao:\n\n" );
        texto.append( mensagemDeErro );

        JOptionPane.showMessageDialog(null, texto, "Resumo da Compilacao", JOptionPane.INFORMATION_MESSAGE );
    }
    
    static void registraErroSintatico( String msg ) throws ErroSintaticoException {
        if ( estadoCompilacao == E_SEM_ERROS ) {
            estadoCompilacao = E_ERRO_SINTATICO;
            mensagemDeErro = msg;
        }
        throw new ErroSintaticoException( msg ); 
    }
    
    static void registraErroSemantico( String msg ) {

        if ( estadoCompilacao == E_SEM_ERROS ) {
            estadoCompilacao = E_ERRO_SEMANTICO;
            mensagemDeErro = msg;
        }
    }
    
    static void regraSemantica( int numeroRegra ) throws ErroSemanticoException {
        System.out.println( "Regra Semantica " + numeroRegra );
        switch ( numeroRegra ) {
            case  0: 	// START
            			codigoPython.append( "const main = () => {\n" );
            			nivelIdentacao++;
			    		break;
            case  1: 	// END
            			codigoPython.append( tabulacao( nivelIdentacao ) );
                		codigoPython.append( "\n}\n\n" );
                		codigoPython.append( "main()\n" );
                		break;
            case  2:	// VAR
            			insereNaTabelaSimbolos( ultimoLexema );
						break;
            case  3:	// METHOD_ASSIGN
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();	
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( nodo_1.getCodigoMinusculo() + " = " + nodo_2.getCodigoMinusculo() + "\n" );
						break;
            case  4:	// VARIAVEL
            			if ( VeSeExisteNaTabelaSimbolos( ultimoLexema ) ) {
				            pilhaSemantica.push( ultimoLexema, 4 );
			            }
			            break;
            case  5:    // MAIS
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + "+" + nodo_2.getCodigoMinusculo(), 5 );
						break;
            case  6:    // MENOS
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + "-" + nodo_2.getCodigoMinusculo(), 6 );
						break;
            case  7:    // VEZES
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + "*" + nodo_2.getCodigoMinusculo(), 7 );
						break;
            case  8:    // DIVIDO
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + "/" + nodo_2.getCodigoMinusculo(), 8 );
						break;
            case  9:    // RESTO
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + "%" + nodo_2.getCodigoMinusculo(), 9 );
						break;
            case 10:    // ELEVADO
            			nodo_2 = pilhaSemantica.pop();
            			nodo_1 = pilhaSemantica.pop();
            			pilhaSemantica.push( nodo_1.getCodigoMinusculo() + "**" + nodo_2.getCodigoMinusculo(), 10 );
            			break;
            case 11:	// UNIQUE_IDENTIFIER
            			if ( VeSeExisteNaTabelaSimbolos( ultimoLexema ) ) {
	            			pilhaSemantica.push( ultimoLexema, 11 );
            			}
            			break;
            case 12:	// NUMERO
            			pilhaSemantica.push( ultimoLexema, 12 );
            			break;
            case 13:	// ABRE E FECHA PAR
            			nodo_1 = pilhaSemantica.pop();
            			pilhaSemantica.push( "(" + nodo_1.getCodigoMinusculo() + ")" , 13 );            
            			break;
            case 14:    // FECHA PAR E CHAVE
		            	nivelIdentacao--;
		    			codigoPython.append( tabulacao( nivelIdentacao ) );
		        		codigoPython.append( "}" );
		        		break;
            case 15:    // WHILE
            			nodo_1 = pilhaSemantica.pop();
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "while(" + nodo_1.getCodigoMinusculo() + ") {\n" );
						nivelIdentacao++;
						break;
            case 16:    // FECHA PAR E CHAVE + QUEBRA LINHA
            			nivelIdentacao--;
            			codigoPython.append( tabulacao( nivelIdentacao ) );
		        		codigoPython.append( "}\n" );
						break;
            case 17:    // WHEN
            			nodo_1 = pilhaSemantica.pop();
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "if(" + nodo_1.getCodigoMinusculo() + ") {\n" );
						nivelIdentacao++;
						break;
            case 18:    // WHEN_NOT
						codigoPython.append( " else {\n" );
						nivelIdentacao++;
						break;
            case 19:    // COND_MAIOR
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + " > " + nodo_2.getCodigoMinusculo(), 19 );
						break;						
            case 20:    // COND_MENOR
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + " < " + nodo_2.getCodigoMinusculo(), 20 );
						break;						
            case 21:    // COND_MAIOR_IGUAL
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + " >= " + nodo_2.getCodigoMinusculo(), 21 );
						break;						
            case 22:    // COND_MENOR_IGUAL
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + " <= " + nodo_2.getCodigoMinusculo(), 22 );
						break;						
            case 23:    // COND_IGUAL
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + " === " + nodo_2.getCodigoMinusculo(), 23 );
						break;						
            case 24:    // COND_DIFERENTE
            			nodo_2 = pilhaSemantica.pop();
						nodo_1 = pilhaSemantica.pop();
						pilhaSemantica.push( nodo_1.getCodigoMinusculo() + " <> " + nodo_2.getCodigoMinusculo(), 24 );
						break;		
            case 25:    // METHOD_LOG
            			nodo_1 = pilhaSemantica.pop();
    					codigoPython.append( tabulacao( nivelIdentacao ) );
    					codigoPython.append( "console.log(" + nodo_1.getCodigoMinusculo() + ")\n" );
    					break;
            case 30:    // FOR 
            			nodo_2 = pilhaSemantica.pop();
                        nodo_1 = pilhaSemantica.pop();
			            nodo_0 = pilhaSemantica.pop();
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "for(" + nodo_0.getCodigoMinusculo() + " = " + nodo_1.getCodigoMinusculo() + "; " + nodo_0.getCodigoMinusculo() + " <= " + nodo_2.getCodigoMinusculo() + "; " + nodo_0.getCodigoMinusculo() + "++) {\n" );
						nivelIdentacao++;
			            break;						
            case 31:    // METHOD_CASE
            			nodo_1 = pilhaSemantica.pop();
            			codigoPython.append( tabulacao( nivelIdentacao ) );
            			codigoPython.append( "switch(" + nodo_1.getCodigoMinusculo() + ") {\n");
						nivelIdentacao++;
						nivelIdentacao++;
						break;
            case 32:    // CASE_WHEN
            			nodo_1 = pilhaSemantica.pop();
            			nivelIdentacao--;
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "case(" + nodo_1.getCodigoMinusculo() + "):\n" );
						nivelIdentacao++;
						break;   
            case 33:    // CASE BREAK
			            codigoPython.append( tabulacao( nivelIdentacao ) );
			            codigoPython.append("break\n");
                        break;	
            case 34:    // CASE DEFAULT BREAK
            			nivelIdentacao--;
		            	codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "default:\n" );
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "break \n" );
						nivelIdentacao--;
						codigoPython.append( tabulacao( nivelIdentacao ) );
						codigoPython.append( "}\n" );
						break;
        }
    }
    
    
    private static int buscaTipoNaTabelaSimbolos(String ultimoLexema ) throws ErroSemanticoException {
    	return tabelaSimbolos.get( ultimoLexema );
	}
    
    private static boolean VeSeExisteNaTabelaSimbolos(String ultimoLexema ) throws ErroSemanticoException {
    	if ( !tabelaSimbolos.containsKey( ultimoLexema ) ) {
	    	throw new ErroSemanticoException( "Variavel " + ultimoLexema + " nao esta declarada! linha: " + linhaAtual );
    	} else {
    		return true;
    	}
	}

	private static void insereNaTabelaSimbolos(String ultimoLexema) throws ErroSemanticoException {
		if ( tabelaSimbolos.containsKey( ultimoLexema ) ) {
	    	throw new ErroSemanticoException( "Variavel " + ultimoLexema + " ja declarada! linha: " + linhaAtual );
		} else {
			tabelaSimbolos.put( ultimoLexema, 0 );
		}
	}
    
	static String tabulacao( int qtd ) {
        StringBuffer sb = new StringBuffer();
        for ( int i=0; i<qtd; i++ ) {
            sb.append( "    " );
        }
        return sb.toString();
    }
		
}

/**
 * Classe Interna para criacao de filtro de selecao
 */
class FiltroSab extends FileFilter {

	public boolean accept(File arg0) {
	   	 if(arg0 != null) {
	         if(arg0.isDirectory()) {
	       	  return true;
	         }
	         if( getExtensao(arg0) != null) {
	        	 if ( getExtensao(arg0).equalsIgnoreCase( "grm" ) ) {
		        	 return true;
	        	 }
	         };
	   	 }
	     return false;
	}

	/**
	 * Retorna quais extensoes poderao ser escolhidas
	 */
	public String getDescription() {
		return "*.grm";
	}
	
	/**
	 * Retorna a parte com a extensao de um arquivo
	 */
	public String getExtensao(File arq) {
	if(arq != null) {
		String filename = arq.getName();
	    int i = filename.lastIndexOf('.');
	    if(i>0 && i<filename.length()-1) {
	    	return filename.substring(i+1).toLowerCase();
	    };
	}
		return null;
	}
}
