package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/procedi-ordine")
public class ProcediOrdine extends HttpServlet {
    private LibroDAO libroDAO = new LibroDAO();
    private SedeDAO sedeDAO = new SedeDAO();
    
    public void setLibroDAO(LibroDAO libroDAO) {
        this.libroDAO = libroDAO;
    }
    
    public void setSedeDAO(SedeDAO sedeDAO) {
        this.sedeDAO = sedeDAO;
    }
    
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }

        List<Sede> sedi = sedeDAO.doRetrivedAll(); //tutte le sedi che abbiamo
        List<Sede> sediDaAggiungere = sedeDAO.doRetrivedAll();
        List<RigaCarrello> righe = (List<RigaCarrello>) session.getAttribute("righeDisponibili");

        if(!righe.isEmpty()){
            for(RigaCarrello r : righe){
                Libro l = r.getLibro();
                //prendo le sedi di ogni libro
                List<Sede> sedeLibro = libroDAO.getPresenzaSede(l.getIsbn());
                for(Sede s : sedi){
                    //se un libro non ha una delle sedi non la rendo visibile al momento della scelta dell'indirizzo
                    if(!(sedeLibro.contains(s)))
                        sediDaAggiungere.remove(s);
                }
            }
        }

        //per la questione sedi non sono molto sicura...perchè si potrebbe anche far arrivare il libro in una sede senza che
        //esso sia già disponibile in quella sede. Da valutare !!!
        request.setAttribute("sedi", sediDaAggiungere);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/procediOrdine.jsp");
        dispatcher.forward(request, response);
    }
}