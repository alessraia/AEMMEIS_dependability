package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/ordine-supporto")
public class OrdineSupporto extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if (Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }

        if (utente == null) { //controllo che l'utente sia in sessione altrimenti non può acquistare
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/login.jsp");
            dispatcher.forward(request, response);
            return;
        }

        //controllo che i libri nel carrello siano tutti disponibili per l'acquisto e aggiungo la lista nella sessione
        Carrello carrello = (Carrello) session.getAttribute("carrello");
        List<RigaCarrello> righe = carrello.getRigheCarrello();
        List<RigaCarrello> nuoveRighe = new ArrayList<RigaCarrello>();
        for(RigaCarrello rigaCarrello : righe){
            if(rigaCarrello.getLibro().isDisponibile()){
                nuoveRighe.add(rigaCarrello);
            }
        }

        session.setAttribute("righeDisponibili", nuoveRighe);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/revisioneOrdine.jsp");
        dispatcher.forward(request, response);
    }
}
