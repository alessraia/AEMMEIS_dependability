package controller.utente;

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
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import org.json.simple.JSONObject;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/aggiungi-carrello")
public class AggiungiCartServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String isbn = request.getParameter("isbn");
        String source= request.getParameter("source");
        String position = request.getParameter("position");

        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }
        else {
            // Utente utente = (Utente) session.getAttribute("utente");
            Carrello carrello = (Carrello) session.getAttribute("carrello");

            String address = "index.html";
            if (source != null) { //ho aggiunto il controllo per source potrebbe essere null
                if (source.equals("mostraLibro"))
                    address = "mostra-libro";
                else if (source.equals("riepilogoOrdine"))
                    address = "riepilogo-ordine";
                else if (source.equals("ricerca")) {
                    address = "ricerca-servlet?q=" + request.getParameter("q");
                } else if (source.equals("aggiungi-carrello")) {
                    address = "mostra-reparto";

                }
            }

            LibroDAO libroService = new LibroDAO();
            Libro libro = libroService.doRetrieveById(isbn);

            List<RigaCarrello> righeCarrello = carrello.getRigheCarrello();

            boolean flag = true; // libro non presente
            if (!righeCarrello.isEmpty()) {
                for (int i = 0; i < righeCarrello.size() && flag; i++) {
                    Libro libroRiga = righeCarrello.get(i).getLibro(); // libro della rigaCarrello
                    if (libroRiga.equals(libro)) {
                        righeCarrello.get(i).setQuantita((righeCarrello.get(i).getQuantita()) + 1); // libro presente, incremento la quantità
                        flag = false; // libro presente
                    }
                }
            }
            if (flag) { // se il libro non è presente, lo aggiungo
                RigaCarrello riga = new RigaCarrello();
                riga.setIdCarrello(carrello.getIdCarrello());
                riga.setLibro(libro);
                riga.setQuantita(1);
                righeCarrello.add(riga);
            }


            session.setAttribute("carrello", carrello);

            if (position != null) {
                address += "#" + position;
            }

            //response.sendRedirect(address);//supporta l'ancoraggio*/
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);
        }
    }

}
