package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/aggiungi-sede")
public class AggiungiSedeServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {

        String citta = request.getParameter("citta");
        String via = request.getParameter("via");
        String civ = request.getParameter("civico");
        String cap = request.getParameter("cap");
        //controllo paramentri del form
        if(citta==null || citta.length()==0 || via==null || via.length()==0|| civ==null || civ.length()==0 ||
                cap==null || cap.length()==0)
            response.sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");

        int civico;
        Sede sede = new Sede();
        try {
            civico = Integer.parseInt(civ);
            sede.setCitta(citta);
            sede.setVia(via);
            sede.setCivico(civico);
            sede.setCap(cap);

            SedeDAO sedeService = new SedeDAO();
            List<Sede> sedi = sedeService.doRetrivedAll();
            boolean flag = true;
            for (Sede s : sedi) {
                if (s.getCap().equals(sede.getCap()) && s.getCitta().equals(sede.getCitta()) && s.getVia().equals(sede.getVia())
                        && s.getCivico() == sede.getCivico()) {
                    request.setAttribute("esito", "non riuscito");//per poter mostrare un errore nell'inserimento
                    RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp");
                    try {
                        dispatcher.forward(request, response);
                    } catch (ServletException e) {
                        log("Errore durante il forward ", e);
                    } catch (IOException e) {
                        log("Errore di I/O durante il forward", e);
                    }
                    flag = false;
                }

            }
            if (flag){
                sedeService.doSave(sede);
            response.sendRedirect("gestisci-sedi");
            }

        }catch (NumberFormatException e){
            response.sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }








    }
}