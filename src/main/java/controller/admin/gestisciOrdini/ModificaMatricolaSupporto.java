package controller.admin.gestisciOrdini;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.gestoreService.Gestore;
import model.gestoreService.GestoreDAO;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/modifica-matricola")
public class ModificaMatricolaSupporto extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        GestoreDAO gestoreDAO = new GestoreDAO();
        OrdineDAO ordineDAO = new OrdineDAO();
        UtenteDAO utenteDAO = new UtenteDAO();

        Utente utente = utenteDAO.doRetrieveById(request.getParameter("utenteScelto"));
        String matricola =request.getParameter("matricolaAttuale");
        String idOrdine = request.getParameter("ordineID");
        Ordine ordine = ordineDAO.doRetrieveById(idOrdine);
        List<Gestore> gestori = gestoreDAO.doRetrivedAll();
        boolean trovato = false;

        //elimino la matricola a cui era stato affidato l'ordine poichè se decido di cambiarla vuol dire che non è disponibile
        for(int i = 0; !trovato && i< gestori.size(); i++){
            if(gestori.get(i).getMatricola().equalsIgnoreCase(matricola)){
                gestori.remove(i);
                trovato = true;
            }
        }

        request.setAttribute("ordineAttuale", ordine);
        request.setAttribute("gestori", gestori);
        request.setAttribute("utenteScelto", utente);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/admin/ordini/modificaMatricola.jsp", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/admin/ordini/modificaMatricola.jsp", e);
        }
    }
}
