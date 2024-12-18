

package br.com.chess.game;

import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.ChessPosition;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.views.BoardView;

import java.util.ArrayList;
import java.util.InputMismatchException;
import java.util.List;
import java.util.Scanner;


public class Main {

    //@ public invariant captureChessPieces.size() >= 0;
    public static List<ChessPiece> captureChessPieces = new ArrayList<>();

    //@ assignable \everything;
    public static void main(String[] args) {
        // write your code here
        Scanner sc = new Scanner(System.in);
        ChessMatch chessMatch = new ChessMatch();
        setBackgroundYellow();
        String init = sc.nextLine();
        if(init.equals("Y")||init.equals("y")||init.equals("yes") || init.equals("YES")){
            while (!chessMatch.isCheckMate()){
                try{
                    resetColor();
                    BoardView.clearScreen();
                    if (captureChessPieces.size() >= 0) {
                        //@ assert captureChessPieces.size() >= 0;
                        BoardView.printMatch(chessMatch, captureChessPieces);
                    }
                    ChessPosition source = BoardView.readChessPosition(sc);
                    boolean[][] possibleMoves = chessMatch.possibleMoves(source);
                    BoardView.clearScreen();
                    BoardView.printBoard(chessMatch.getChessPieces(),possibleMoves);
                    print02();
                    ChessPosition target  = BoardView.readChessPosition(sc);
                    //@ nullable
                    ChessPiece capturedPiece = chessMatch.performChessMove(source, target);
                    if(capturedPiece != null && captureChessPieces.size() >= 0){
                        //@ assert captureChessPieces.size() >= 0;
                        captureChessPieces.add(capturedPiece);
                    }
                    if(chessMatch.getPromoted() != null){
                        print03();
                        String type = sc.nextLine();
                        chessMatch.replacepromotedChessPiece(type);
                    }
                }
                catch (ChessException | InputMismatchException e) {
                    printErrorMessage(e);
                    sc.nextLine();
                }
            }

            BoardView.clearScreen();
            BoardView.printMatch(chessMatch, captureChessPieces);

        }else {
            fecharSys();
        }

    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void setBackgroundYellow() {
        System.out.print("\u001B[43m");
        System.out.print("\u001B[30m");
        System.out.println("BEM VINDO AO JOGO DE XADREZ PARA CONSOLE\n\n" +
                "O game foi desenvolvido por Luis Fernando Poma Mamani\n"+
                "Durante o curso de Java com POO criado pelo professor\n"+
                "Nélio Alves");
        System.out.print("Para iniciar o jogo Digite y ou yes :");
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void resetColor() {
        System.out.print("\u001B[0m");
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void print01() {
        System.out.println();
        System.out.print("Posição de origem: ");
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void print02() {
        System.out.println();
        System.out.print("Posição de destino: ");
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void print03() {
        System.out.println("Digite a letra da peça a ser escolhida: (A/C/T/B)");
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void fecharSys() {
        System.out.close();
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void printErrorMessage(Exception e) {
        System.out.println(e.getMessage());
    }

}
